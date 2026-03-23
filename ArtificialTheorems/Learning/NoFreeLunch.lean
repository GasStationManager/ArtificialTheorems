/-
No Free Lunch Theorem (Wolpert 1996) - Proof

Wolpert, D.H. "The Lack of A Priori Distinctions Between Learning Algorithms."
Neural Computation 8.7 (1996): 1341–1390.

The key idea: define an involution flip_x on (X → Bool) that flips f at x
and preserves f on S. For each pair {f, flip_x(f)}, exactly one is in the
error set. Since the involution is fixed-point-free and pairs up all 2^|X|
functions, exactly half (= 2^(|X|-1)) are errors.
-/

import Mathlib

open Finset Function

variable {X : Type*} [DecidableEq X] [Fintype X]

/-- Restrict a function f : X → Bool to a subset S, yielding a function on S. -/
def restrictToFinset (f : X → Bool) (S : Finset X) : S → Bool :=
  fun ⟨x, _⟩ => f x

/-- A deterministic learner: given labeled examples on S, produces a hypothesis on all of X. -/
def Learner (X : Type*) (S : Finset X) :=
  (S → Bool) → X → Bool

/-- The set of target functions that the learner gets wrong at point x. -/
def errSet (S : Finset X) (A : Learner X S) (x : X) : Finset (X → Bool) :=
  Finset.univ.filter fun f => A (restrictToFinset f S) x != f x

/-- The set of target functions that the learner gets right at point x. -/
def corrSet (S : Finset X) (A : Learner X S) (x : X) : Finset (X → Bool) :=
  Finset.univ.filter fun f => A (restrictToFinset f S) x == f x

/-- Flip f at x: negate f(x), keep everything else. -/
def flipAt (x : X) (f : X → Bool) : X → Bool :=
  Function.update f x (!f x)

/-- flipAt is an involution. -/
theorem flipAt_involutive (x : X) : Function.Involutive (flipAt x : (X → Bool) → X → Bool) := by
  intro f
  funext y
  simp only [flipAt, Function.update_apply]
  split
  · subst_vars; simp [Bool.not_not]
  · rfl

/-- flipAt preserves the restriction to S when x ∉ S. -/
theorem flipAt_restrict (S : Finset X) (x : X) (hx : x ∉ S) (f : X → Bool) :
    restrictToFinset (flipAt x f) S = restrictToFinset f S := by
  funext ⟨y, hy⟩
  have hne : y ≠ x := fun h => hx (h ▸ hy)
  simp [restrictToFinset, flipAt, Function.update_apply, hne]

/-- errSet and corrSet are disjoint. -/
theorem errSet_disjoint_corrSet (S : Finset X) (A : Learner X S) (x : X) :
    Disjoint (errSet S A x) (corrSet S A x) := by
  rw [errSet, corrSet, Finset.disjoint_filter]
  intro f _ h1 h2
  revert h1 h2
  cases A (restrictToFinset f S) x <;> cases f x <;> simp

/-- errSet and corrSet cover all functions. -/
theorem errSet_union_corrSet (S : Finset X) (A : Learner X S) (x : X) :
    errSet S A x ∪ corrSet S A x = Finset.univ := by
  rw [errSet, corrSet]
  ext f
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  cases A (restrictToFinset f S) x <;> cases f x <;> simp

/-- errSet and corrSet partition all functions. -/
theorem errSet_add_corrSet (S : Finset X) (A : Learner X S) (x : X) :
    (errSet S A x).card + (corrSet S A x).card = Fintype.card (X → Bool) := by
  rw [← Finset.card_union_of_disjoint (errSet_disjoint_corrSet S A x)]
  rw [errSet_union_corrSet]
  rfl

/-- Cardinality of all functions X → Bool. -/
theorem card_fun_bool : Fintype.card (X → Bool) = 2 ^ Fintype.card X := by
  simp [Fintype.card_bool]

/-- Helper: flipAt x maps f in errSet to flipAt x f in corrSet. -/
private theorem flipAt_err_to_corr (S : Finset X) (A : Learner X S) (x : X) (hx : x ∉ S)
    (f : X → Bool) (hf : f ∈ errSet S A x) :
    flipAt x f ∈ corrSet S A x := by
  rw [errSet, Finset.mem_filter] at hf
  rw [corrSet, Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
  obtain ⟨_, hf⟩ := hf
  rw [flipAt_restrict S x hx]
  show (A (restrictToFinset f S) x == flipAt x f x) = true
  simp only [flipAt, Function.update_apply, if_pos rfl]
  revert hf
  cases A (restrictToFinset f S) x <;> cases f x <;> simp

/-- Helper: flipAt x maps f in corrSet to flipAt x f in errSet. -/
private theorem flipAt_corr_to_err (S : Finset X) (A : Learner X S) (x : X) (hx : x ∉ S)
    (f : X → Bool) (hf : f ∈ corrSet S A x) :
    flipAt x f ∈ errSet S A x := by
  rw [corrSet, Finset.mem_filter] at hf
  rw [errSet, Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
  obtain ⟨_, hf⟩ := hf
  rw [flipAt_restrict S x hx]
  show (A (restrictToFinset f S) x != flipAt x f x) = true
  simp only [flipAt, Function.update_apply, if_pos rfl]
  revert hf
  cases A (restrictToFinset f S) x <;> cases f x <;> simp

/-- flipAt maps errSet bijectively to corrSet. -/
theorem flipAt_errSet_bij (S : Finset X) (A : Learner X S) (x : X) (hx : x ∉ S) :
    (errSet S A x).card = (corrSet S A x).card := by
  apply Finset.card_nbij (flipAt x)
  · exact flipAt_err_to_corr S A x hx
  · intro f₁ _ f₂ _ h
    exact (flipAt_involutive x).injective h
  · intro f hf
    exact ⟨flipAt x f, flipAt_corr_to_err S A x hx f hf, flipAt_involutive x f⟩

/-- **No Free Lunch Theorem**: For any learner A, any test point x ∉ S,
    exactly half of all target functions f : X → Bool are misclassified at x.
    That is, |{f | A(f|_S)(x) ≠ f(x)}| = 2^(|X| - 1). -/
theorem no_free_lunch
    (S : Finset X) (A : Learner X S) (x : X) (hx : x ∉ S) :
    (errSet S A x).card = 2 ^ (Fintype.card X - 1) := by
  have hpart := errSet_add_corrSet S A x
  have hbij := flipAt_errSet_bij S A x hx
  have htotal : Fintype.card (X → Bool) = 2 ^ Fintype.card X := card_fun_bool
  -- We have: card E + card C = 2^n and card E = card C
  -- So 2 * card E = 2^n, hence card E = 2^(n-1)
  have key : (errSet S A x).card + (errSet S A x).card = 2 ^ Fintype.card X := by
    omega
  cases hn : Fintype.card X with
  | zero =>
    -- X is empty, so x cannot exist
    exact absurd (Fintype.card_pos_iff.mpr ⟨x⟩) (by omega)
  | succ n =>
    rw [hn] at key
    simp only [Nat.succ_sub_one]
    have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    omega

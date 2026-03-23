/-
No Free Lunch Theorem (Wolpert 1996) - Specification

Wolpert, D.H. "The Lack of A Priori Distinctions Between Learning Algorithms."
Neural Computation 8.7 (1996): 1341–1390.

For a finite domain X with binary labels, any deterministic learning algorithm
achieves expected off-training-set error exactly 1/2, averaged uniformly over
all target functions f : X → Bool.

Concretely: for any x ∉ S (training set), exactly half of all functions
f : X → Bool satisfy A(f|_S)(x) ≠ f(x), where A is any deterministic learner.
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

/-- **No Free Lunch Theorem**: For any learner A, any test point x ∉ S,
    exactly half of all target functions f : X → Bool are misclassified at x.
    That is, |{f | A(f|_S)(x) ≠ f(x)}| = 2^(|X| - 1). -/
theorem no_free_lunch
    (S : Finset X) (A : Learner X S) (x : X) (hx : x ∉ S) :
    (errSet S A x).card = 2 ^ (Fintype.card X - 1) := by
  sorry

/-
Integer-rounded Value Iteration - Specification

Defines an integer-rounded Bellman operator for finite MDPs that computes the
rational Bellman operator and then rounds each state's value to the nearest integer.

Proves approximate convergence:
- Convergence of the iterates (after casting to reals) to the true fixed point
  of the real Bellman operator up to a radius induced by rounding.
- Explicit geometric error bound: for discount 0 ≤ γ < 1, the iterate error is
  bounded by (γ^n) * initial_error + (1/2) / (1-γ) in sup-norm.
- Eventual inclusion in any ball of radius ε > (1/2)/(1-γ).
-/

import Mathlib
import ArtificialTheoremsSpec.RL.ValueIterationCompleteSpec

open Metric Filter Topology

namespace ApproxValueIterationInt

variable {S A : Type} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq A]

open scoped BigOperators

-- Cast helpers
def castZtoQ (v : S → ℤ) : S → ℚ := fun s => (v s : ℚ)
noncomputable def castQtoR (v : S → ℚ) : S → ℝ := fun s => (v s : ℝ)
noncomputable def castZtoR (v : S → ℤ) : S → ℝ := fun s => ((v s : ℚ) : ℝ)

-- Nearest-integer rounding on ℚ (using Mathlib's `round`, halves toward +∞)
def roundNearestRat (q : ℚ) : ℤ := round q

-- Integer-rounded Bellman operator
def bellmanOperatorInt (mdp : MDP S A) (γ : ℚ) (v : S → ℤ) : S → ℤ :=
  fun s =>
    let qVal : A → ℚ := fun a =>
      mdp.R s a + γ * Finset.univ.sum (fun s' => mdp.P s a s' * (v s' : ℚ))
    roundNearestRat (Finset.univ.sup' Finset.univ_nonempty qVal)

/-- Approximate convergence of integer value iteration.

For discount 0 ≤ γ < 1, the iterate error is bounded by:
  γ^n * dist(v₀, v*) + (1/2) / (1-γ) -/
theorem INT_VALUE_ITERATION_APPROX
    (mdp : MDP S A) (γ : ℚ) (hγ_nonneg : 0 ≤ γ) (hγ_lt : γ < 1) :
    ∃ v_star : S → ℝ,
      bellmanOperatorReal (S:=S) (A:=A) mdp (γ : ℝ) v_star = v_star ∧
      ∀ (v₀ : S → ℤ) (n : ℕ),
        dist (castZtoR ((bellmanOperatorInt (S:=S) (A:=A) mdp γ)^[n] v₀)) v_star
          ≤ (γ : ℝ)^n * dist (castZtoR v₀) v_star +
            ((1 : ℝ) / 2) / (1 - (γ : ℝ)) := by
  sorry

/-- Eventual ball inclusion.

For any ε > (1/2)/(1-γ), the iterates eventually stay within distance ε of v*. -/
theorem INT_VALUE_ITERATION_EVENTUAL_BALL
    (mdp : MDP S A) (γ : ℚ) (hγ_nonneg : 0 ≤ γ) (hγ_lt : γ < 1)
    (ε : ℝ) (hε : ((1 : ℝ) / 2) / (1 - (γ : ℝ)) < ε) :
    ∀ v₀ : S → ℤ, ∀ᶠ n in atTop,
      let v_starWitness := Classical.choose
        (INT_VALUE_ITERATION_APPROX (S:=S) (A:=A) mdp γ hγ_nonneg hγ_lt)
      have hfix := (Classical.choose_spec
        (INT_VALUE_ITERATION_APPROX (S:=S) (A:=A) mdp γ hγ_nonneg hγ_lt)).1
      let v_star : S → ℝ := v_starWitness
      dist (castZtoR ((bellmanOperatorInt (S:=S) (A:=A) mdp γ)^[n] v₀)) v_star ≤ ε := by
  sorry

end ApproxValueIterationInt

/-
Value Iteration Algorithm for Markov Decision Processes - Specification

Proof of convergence via Banach's fixed point theorem, with a noncomputable
Bellman operator defined over Reals; then showing that the computable,
rational number version of Bellman operator is equivalent.
-/

import Mathlib

open Metric Filter Topology

-- ================================
-- MDP STRUCTURE
-- ================================

structure MDP (S : Type) (A : Type) [Fintype S] where
  P : S → A → S → ℚ
  R : S → A → ℚ
  P_nonneg : ∀ s a s', 0 ≤ P s a s'
  P_sum_one : ∀ s a, (Finset.univ : Finset S).sum (P s a) = 1

variable {S A : Type} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq A]

-- Rational Bellman operator
def bellmanOperatorRat (mdp : MDP S A) (γ : ℚ) (v : S → ℚ) : S → ℚ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty fun a =>
    mdp.R s a + γ * Finset.univ.sum fun s' => mdp.P s a s' * v s'

-- Real Bellman operator
noncomputable def bellmanOperatorReal (mdp : MDP S A) (γ : ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty fun a =>
    (mdp.R s a : ℝ) + γ * Finset.univ.sum fun s' => (mdp.P s a s' : ℝ) * v s'

-- Cast helper
def castToReal {S : Type} (v : S → ℚ) : S → ℝ := fun s => ((v s) : ℝ)

/-- **THE MAIN RESULT**: Value iteration converges with all guarantees -/
theorem VALUE_ITERATION_CONVERGENCE_COMPLETE (mdp : MDP S A) (γ : Rat)
    (hγ_nonneg : 0 ≤ γ) (hγ_lt : γ < 1) :
    ∃ v_star : S → ℝ,
    -- 1. v_star is the optimal value function (Bellman equation)
    bellmanOperatorReal mdp γ v_star = v_star ∧
    -- 2. Value iteration converges to v_star from any starting point
    (∀ v₀ : S → Rat, Tendsto (fun n => castToReal ((bellmanOperatorRat mdp γ)^[n] v₀)) atTop (𝓝 v_star)) ∧
    -- 3. Geometric convergence with explicit rate
    (∀ v₀ : S → Rat, ∀ n : ℕ,
      dist (castToReal ((bellmanOperatorRat mdp γ)^[n] v₀)) v_star ≤
      dist v₀ (bellmanOperatorRat mdp γ v₀) * γ^n / (1 - γ)) ∧
    -- 4. Uniqueness: any fixed point of the Bellman operator equals v_star
    (∀ v' : S → ℝ, bellmanOperatorReal mdp γ v' = v' → v' = v_star) := by
  sorry

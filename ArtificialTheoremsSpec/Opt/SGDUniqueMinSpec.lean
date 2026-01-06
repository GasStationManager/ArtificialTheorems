/-
SGD Convergence with Unique Minimizer - Specification

This file specifies the corollary to the SGD convergence theorem
in the case where the drift condition has a unique zero.
-/

import Mathlib
import ArtificialTheoremsSpec.Opt.SGDSpec

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace BigOperators

namespace SGDUniqueMin

variable {Ω : Type*} [m0 : MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/-- Simplified SGD assumptions for unbiased gradients with bounded variance.

This extends SGD_Convergence_Assumptions with:
- R = 0 (unbiased gradients)
- Constant variance bound σ² (not state-dependent)
- Unique zero of drift (for convergence to x*)

The key benefit is that we can reuse convergence_stochastic_gradient_method
directly for drift summability and V convergence.
-/
structure SimplifiedAssumptions
    (X : ℕ → Ω → E)
    (γ : ℕ → ℝ)
    (h : E → E)
    (ΔM : ℕ → Ω → E)
    (V : E → ℝ)
    (gradV : E → E)
    (ℱ : Filtration ℕ m0)
    (x_star : E) : Prop where

  /-- Base SGD assumptions with R = 0.
      This gives us convergence_stochastic_gradient_method for free. -/
  base : SGD_Convergence_Assumptions μ X γ h ΔM (fun _ _ => 0) V gradV ℱ

  /-- KEY SIMPLIFICATION: Variance bound is CONSTANT, not state-dependent.
      This is stronger than base.martingale_condvar_bound and makes
      the noise summability argument much simpler. -/
  martingale_condvar_bound_const : ∃ σ : ℝ, 0 < σ ∧ ∀ n,
    μ[fun ω => ‖ΔM (n + 1) ω‖^2 | ℱ n] ≤ᵐ[μ] fun _ => σ^2

  /-- Recursion matches the StochasticAlgorithm form with R = 0. -/
  recursion : ∀ n ω, X (n + 1) ω = X n ω - (γ (n + 1)) • h (X n ω) + (γ (n + 1)) • ΔM (n + 1) ω

  /-- Unique zero of drift - this is what makes convergence to x* work. -/
  drift_zero_unique : {x : E | @inner ℝ _ _ (gradV x) (h x) = 0} = {x_star}

/-- Simplified Corollary 2.3.1: Almost sure convergence for unbiased SGD with bounded variance.

Under the simplified assumptions (unbiased gradients, constant variance bound), we have:
- X_n → x* almost surely

The proof is simpler because:
1. No remainder term R (so the earlier "line 1375" gap disappears)
2. Constant variance ⟹ E[‖∑ γ_k ΔM_k‖²] ≤ σ² ∑ γ_k² < ∞ directly
3. L²-bounded martingale converges a.s. by Doob's theorem
-/
theorem convergence_simplified
    (X : ℕ → Ω → E) (γ : ℕ → ℝ) (h : E → E) (ΔM : ℕ → Ω → E)
    (V : E → ℝ) (gradV : E → E) (ℱ : Filtration ℕ m0) (x_star : E)
    (asm : SimplifiedAssumptions μ X γ h ΔM V gradV ℱ x_star) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (nhds x_star) := by
  sorry

end SGDUniqueMin

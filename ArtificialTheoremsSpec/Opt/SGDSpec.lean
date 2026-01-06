/-
Stochastic Gradient Descent Convergence - Specification
-/

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology BigOperators
open scoped RealInnerProductSpace

variable {Ω : Type*} [m0 : MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Stochastic Algorithm recursion defined in Eq (2.5):
X_{n+1} = X_n - γ_{n+1} h(X_n) + γ_{n+1}(ΔM_{n+1} + R_{n+1}) -/
def StochasticAlgorithm (X : ℕ → Ω → E) (γ : ℕ → ℝ) (h : E → E) (ΔM R : ℕ → Ω → E) : Prop :=
  ∀ n ω, X (n + 1) ω = X n ω - (γ (n + 1)) • h (X n ω) + (γ (n + 1)) • (ΔM (n + 1) ω + R (n + 1) ω)

/-- Assumptions for Theorem 2.3.6.
Encapsulates H1 (Drift), H2 (Perturbations), and step size conditions. -/
structure SGD_Convergence_Assumptions
    (X : ℕ → Ω → E)
    (γ : ℕ → ℝ)
    (h : E → E)
    (ΔM R : ℕ → Ω → E)
    (V : E → ℝ)
    (gradV : E → E)
    (ℱ : Filtration ℕ m0) : Prop where

  -- Step Size Conditions (Eq 2.6)
  gamma_pos : ∀ n, 0 < γ n
  gamma_sum_inf : ¬ Summable γ
  gamma_sq_sum_fin : Summable (fun n => (γ n) ^ 2)
  gamma_le_one : ∀ n, γ n ≤ 1

  -- Regularity of V (C² L-smooth / sub-quadratic)
  V_smooth : ContDiff ℝ 2 V
  V_grad_eq : ∀ x, gradient V x = gradV x
  V_grad_lipschitz : ∃ L : ℝ, 0 < L ∧ ∀ x y, ‖gradV x - gradV y‖ ≤ L * ‖x - y‖

  -- (H1) Drift Assumptions
  V_lower_bound : ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ V x
  V_coercive : Tendsto V (cocompact E) atTop
  drift_nonneg : ∀ x, 0 ≤ @inner ℝ _ _ (gradV x) (h x)
  growth_bound : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖h x‖^2 + ‖gradV x‖^2 ≤ C * (1 + V x)

  -- Regularity of drift direction
  h_continuous : Continuous h

  -- (H2) Perturbations
  -- (i) ΔM is a martingale difference sequence with conditional variance bound
  martingale_diff_adapted : Adapted ℱ ΔM
  martingale_diff_condexp : ∀ n, μ[ΔM (n + 1)|ℱ n] =ᵐ[μ] 0
  martingale_condvar_bound : ∃ C : ℝ, 0 < C ∧ ∀ n,
    μ[fun ω => ‖ΔM (n + 1) ω‖^2 | ℱ n] ≤ᵐ[μ] fun ω => C * (1 + V (X n ω))
  martingale_diff_L2 : ∀ n, Integrable (fun ω => ‖ΔM (n + 1) ω‖^2) μ

  -- (ii) R is predictable with conditional variance bound
  remainder_adapted : Adapted ℱ R
  remainder_condvar_bound : ∃ C : ℝ, 0 < C ∧ ∀ n,
    μ[fun ω => ‖R (n + 1) ω‖^2 | ℱ n] ≤ᵐ[μ] fun ω => C * (γ (n + 1))^2 * (1 + V (X n ω))
  remainder_L2 : ∀ n, Integrable (fun ω => ‖R (n + 1) ω‖^2) μ

  -- Process adaptedness
  X_adapted : Adapted ℱ X

  -- Initial condition has finite expected energy
  V_X0_integrable : Integrable (fun ω => V (X 0 ω)) μ

/-- Theorem 2.3.6: Convergence of the Stochastic Gradient Method.

Under assumptions (H1) and (H2), one has:
(a) sup_{n≥0} E[V(X_n)] < +∞
(b) ∑_{n≥0} γ_{n+1}⟨∇V, h⟩(X_n) < +∞ a.s.
(c) V(X_n) → V_∞ ∈ L¹ a.s.
(d) X_n - X_{n-1} → 0 a.s. and in L²
-/
theorem convergence_stochastic_gradient_method
    (X : ℕ → Ω → E) (γ : ℕ → ℝ) (h : E → E) (ΔM R : ℕ → Ω → E) (V : E → ℝ) (gradV : E → E)
    (ℱ : Filtration ℕ m0)
    (proc : StochasticAlgorithm X γ h ΔM R)
    (asm : SGD_Convergence_Assumptions μ X γ h ΔM R V gradV ℱ) :
    -- (a) sup E[V(X_n)] < +∞
    (BddAbove (Set.range fun n => ∫ ω, V (X n ω) ∂μ)) ∧
    -- (b) ∑ γ_{n+1}⟨∇V, h⟩(X_n) < +∞ a.s.
    (∀ᵐ ω ∂μ, Summable (fun n => γ (n + 1) * @inner ℝ _ _ (gradV (X n ω)) (h (X n ω)))) ∧
    -- (c) V(X_n) → V_∞ ∈ L¹ a.s.
    (∃ V_inf : Ω → ℝ, Integrable V_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => V (X n ω)) atTop (nhds (V_inf ω))) ∧
    -- (d) X_{n+1} - X_n → 0 a.s. and in L²
    (∀ᵐ ω ∂μ, Tendsto (fun n => X (n + 1) ω - X n ω) atTop (nhds 0)) ∧
    (Tendsto (fun n => ∫ ω, ‖X (n + 1) ω - X n ω‖^2 ∂μ) atTop (nhds 0)) := by
  sorry

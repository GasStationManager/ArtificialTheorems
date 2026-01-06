/-
Robbins-Siegmund Theorem - Specification
-/

import Mathlib

open MeasureTheory Filter
open scoped ProbabilityTheory BigOperators NNReal

namespace QLS
namespace Stoch

/-- Cumulative product `∏_{k < t} (1 + Y_{k+1})`. -/
noncomputable def prodY (Y : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range t).prod fun k => 1 + Y (k + 1) ω

/-- Robbins–Siegmund variant under expectation-level summability and a uniform product bound.

Assumptions:
- Adaptedness/predictability for `X,Y,Z,W` as in the main theorem
- Nonnegativity: `0 ≤ X t ω, 0 ≤ Y t ω, 0 ≤ Z t ω, 0 ≤ W t ω`
- Integrability: `X t, Z t, W t` integrable for all `t`
- Drift: `μ[X_{t+1} | ℱ_t] ≤ (1+Y_{t+1}) X_t + Z_{t+1} - W_{t+1}` a.e.
- Expectation summability: `Summable (fun t => ∫ ω, Z t ω ∂μ)`
- Product bound: `∃ C > 0, ∀ t ω, prodY Y t ω ≤ C`

Conclusions:
- `X t` converges almost surely to a finite limit
- `∑ W t` is finite almost surely
-/
theorem robbinsSiegmund_expBound
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m0)
    (X Y Z W : ℕ → Ω → ℝ)
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y)
    (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Y : Adapted ℱ fun t => Y (t + 1))
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (predictable_W : Adapted ℱ fun t => W (t + 1))
    (hX_nonneg : ∀ t ω, 0 ≤ X t ω)
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω)
    (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (condexp_ineq : ∀ t,
      μ[fun ω => X (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_Z : ∀ t, Integrable (Z t) μ)
    (integrable_W : ∀ t, Integrable (W t) μ)
    (sumEZ : Summable (fun t => ∫ ω, Z t ω ∂μ))
    (prod_bound : ∃ C : ℝ, 0 < C ∧ ∀ t ω, prodY Y t ω ≤ C)
  : ∃ Xlim : Ω → ℝ,
      (∀ᵐ ω ∂μ, Tendsto (fun t => X t ω) atTop (nhds (Xlim ω))) ∧
      (∀ᵐ ω ∂μ, Summable (fun t => W t ω)) := by
  sorry

/-- Full Robbins-Siegmund theorem with L¹ limit and sup E[V] bound.

Assumptions:
- Adaptedness/predictability for `V, α, β, U`
- Nonnegativity: `0 ≤ V t ω, 0 ≤ α t ω, 0 ≤ β t ω, 0 ≤ U t ω`
- Integrability: `V t, β t, U t` integrable for all `t`
- Product bound: `∃ C > 0, ∀ t ω, prodY α t ω ≤ C`
- Summability: `Summable (fun t => ∫ ω, β t ω ∂μ)`
- Drift inequality: `μ[V_{t+1} | ℱ_t] ≤ (1+α_{t+1}) V_t + β_{t+1} - U_{t+1}` a.e.

Conclusions:
- `V_n → V_∞` a.s. with `V_∞ ∈ L¹`
- `sup E[V_n] < ∞`
- `∑ U_n < ∞` a.s.
-/
theorem robbinsSiegmund_full
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0)
    (V U α β : ℕ → Ω → ℝ)
    -- Adaptedness
    (adapted_V : Adapted ℱ V)
    (adapted_α : Adapted ℱ α)
    (adapted_β : Adapted ℱ β)
    (adapted_U : Adapted ℱ U)
    -- Predictability (X_{n+1} is F_n-measurable)
    (predictable_α : Adapted ℱ fun t => α (t + 1))
    (predictable_β : Adapted ℱ fun t => β (t + 1))
    (predictable_U : Adapted ℱ fun t => U (t + 1))
    -- Nonnegativity
    (hV_nonneg : ∀ t ω, 0 ≤ V t ω)
    (hα_nonneg : ∀ t ω, 0 ≤ α t ω)
    (hβ_nonneg : ∀ t ω, 0 ≤ β t ω)
    (hU_nonneg : ∀ t ω, 0 ≤ U t ω)
    -- Integrability
    (integrable_V : ∀ t, Integrable (V t) μ)
    (integrable_β : ∀ t, Integrable (β t) μ)
    (integrable_U : ∀ t, Integrable (U t) μ)
    -- (ii) Product bound and β summability
    (prod_bound : ∃ C : ℝ, 0 < C ∧ ∀ t ω, prodY α t ω ≤ C)
    (sum_Eβ : Summable (fun t => ∫ ω, β t ω ∂μ))
    -- (iii) Drift inequality
    (condexp_ineq : ∀ t,
      μ[fun ω => V (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => (1 + α (t + 1) ω) * V t ω + β (t + 1) ω - U (t + 1) ω)
  : -- Conclusions
    -- (a) V_n → V_∞ a.s. with V_∞ ∈ L¹, and sup E[V_n] < ∞
    (∃ Vlim : Ω → ℝ,
      Integrable Vlim μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun t => V t ω) atTop (nhds (Vlim ω)))) ∧
    (BddAbove (Set.range fun n => ∫ ω, V n ω ∂μ)) ∧
    -- (b) ∑ U_n < ∞ a.s.
    (∀ᵐ ω ∂μ, Summable (fun t => U t ω)) := by
  sorry

end QLS.Stoch

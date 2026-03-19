/-
Universal Approximation Theorem (Cybenko 1989) - Specification

Cybenko, G. "Approximation by Superpositions of a Sigmoidal Function."
Mathematics of Control, Signals, and Systems 2 (1989): 303–314.

The theorem states that finite sums of the form ∑ αⱼ σ(wⱼᵀx + bⱼ)
are dense in C(Iₙ) for the unit hypercube Iₙ ⊂ ℝⁿ, where σ is any
continuous sigmoidal function.

The proof assumes the Jordan decomposition of continuous linear functionals
on C(K,ℝ) (every bounded linear functional is the difference of two positive
ones). This is a classical result from functional analysis not yet in Mathlib;
see the proof file for detailed references.
-/

import Mathlib

open MeasureTheory Topology ContinuousMap Set Filter

noncomputable section

variable {n : ℕ}

-- The unit hypercube Iₙ = [0,1]ⁿ
def UnitCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc 0 1)

/-- A single-hidden-layer neural network function on ℝⁿ:
    x ↦ ∑ⱼ αⱼ · σ(⟨wⱼ, x⟩ + bⱼ) -/
def neuralNetFun (σ : ℝ → ℝ) (N : ℕ)
    (w : Fin N → (Fin n → ℝ))
    (b : Fin N → ℝ)
    (α : Fin N → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ j : Fin N, α j * σ (∑ i : Fin n, w j i * x i + b j)

/-- σ : ℝ → ℝ is sigmoidal if σ(t) → 1 as t → +∞ and σ(t) → 0 as t → −∞. -/
def IsSigmoidal (σ : ℝ → ℝ) : Prop :=
  Tendsto σ atTop (nhds 1) ∧ Tendsto σ atBot (nhds 0)

/-- A continuous linear functional is positive if it maps nonneg functions to nonneg reals. -/
def IsPositiveLinearFunctional
    (L : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ f : C(↥(UnitCube n), ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f

/-- Jordan decomposition of continuous linear functionals on C(Iₙ,ℝ):
    every bounded linear functional is the difference of two positive ones.

    Classical result (Rudin RCA Thm 6.19 + 6.12; Aliprantis & Border Thms 9.11, 9.14).
    Not in Mathlib v4.27.0 (no BanachLattice class, no signed RMK). -/
def HasJordanDecomposition (n : ℕ) : Prop :=
  ∀ (L : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ),
    ∃ (Lpos Lneg : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ),
      IsPositiveLinearFunctional Lpos ∧
      IsPositiveLinearFunctional Lneg ∧
      ∀ f, L f = Lpos f - Lneg f

/-- **Cybenko's Universal Approximation Theorem (1989).**

For any continuous sigmoidal σ : ℝ → ℝ and any continuous f : Iₙ → ℝ,
the neural network functions ∑ αⱼ σ(⟨wⱼ, x⟩ + bⱼ) can approximate f
uniformly to arbitrary precision on the unit hypercube.

More precisely: for any ε > 0, there exist N, weights w, biases b,
and coefficients α such that |f(x) - ∑ αⱼ σ(⟨wⱼ, x⟩ + bⱼ)| < ε
for all x ∈ Iₙ.

Assumes the Jordan decomposition of functionals on C([0,1]ⁿ,ℝ) as a
premise. See `HasJordanDecomposition` and the proof file for references. -/
theorem universal_approximation_cybenko
    (hJD : HasJordanDecomposition n)
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (f : (Fin n → ℝ) → ℝ) (hf_cont : ContinuousOn f (UnitCube n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (w : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ) (α : Fin N → ℝ),
      ∀ x ∈ UnitCube n,
        |f x - neuralNetFun σ N w b α x| < ε := by
  sorry

end

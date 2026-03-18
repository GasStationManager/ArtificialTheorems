/-
Universal Approximation Theorem (Cybenko 1989) - Specification

Cybenko, G. "Approximation by Superpositions of a Sigmoidal Function."
Mathematics of Control, Signals, and Systems 2 (1989): 303–314.

The theorem states that finite sums of the form ∑ αⱼ σ(wⱼᵀx + bⱼ)
are dense in C(Iₙ) for the unit hypercube Iₙ ⊂ ℝⁿ, where σ is any
continuous sigmoidal function.

The proof proceeds in two steps:
1. Define "discriminatory" functions: σ is discriminatory if the only
   signed finite regular Borel measure μ on Iₙ satisfying
   ∫ σ(⟨w, x⟩ + b) dμ = 0 for all w ∈ ℝⁿ, b ∈ ℝ is μ = 0.
2. Show that continuous sigmoidal functions are discriminatory
   (via bounded convergence + measure theory).
3. Show that discriminatory ⟹ the span is dense in C(Iₙ)
   (via Hahn-Banach + Riesz representation).
-/

import Mathlib

open MeasureTheory Topology ContinuousMap Set Filter

noncomputable section

variable {n : ℕ}

-- The unit hypercube Iₙ = [0,1]ⁿ as a compact space
abbrev UnitCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Set.pi Set.univ (fun _ => Set.Icc 0 1)

-- The neural network function class: finite sums ∑ αⱼ σ(⟨wⱼ, x⟩ + bⱼ)
/-- A single-hidden-layer neural network function on ℝⁿ:
    x ↦ ∑ⱼ αⱼ · σ(⟨wⱼ, x⟩ + bⱼ) -/
def neuralNetFun (σ : ℝ → ℝ) (N : ℕ)
    (w : Fin N → EuclideanSpace ℝ (Fin n))
    (b : Fin N → ℝ)
    (α : Fin N → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j : Fin N, α j * σ (inner (w j) x + b j)

/-- σ : ℝ → ℝ is sigmoidal if σ(t) → 1 as t → +∞ and σ(t) → 0 as t → −∞. -/
def IsSigmoidal (σ : ℝ → ℝ) : Prop :=
  Tendsto σ atTop (nhds 1) ∧ Tendsto σ atBot (nhds 0)

/-- σ is discriminatory on Iₙ if for any signed finite regular Borel measure μ,
    (∀ w b, ∫ x in UnitCube n, σ(⟨w, x⟩ + b) dμ = 0) → μ = 0. -/
def IsDiscriminatory (σ : ℝ → ℝ) : Prop :=
  ∀ (μ : SignedMeasure (EuclideanSpace ℝ (Fin n))),
    (∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ),
      μ.restrict (UnitCube n) (fun x => σ (inner w x + b)) = 0) →
    μ.restrict (UnitCube n) = 0

/-- **Cybenko's Universal Approximation Theorem (1989).**

For any continuous sigmoidal σ : ℝ → ℝ and any continuous f : Iₙ → ℝ,
the neural network functions ∑ αⱼ σ(⟨wⱼ, x⟩ + bⱼ) can approximate f
uniformly to arbitrary precision.

More precisely: for any ε > 0, there exist N, weights w, biases b,
and coefficients α such that |f(x) - ∑ αⱼ σ(⟨wⱼ, x⟩ + bⱼ)| < ε
for all x ∈ Iₙ. -/
theorem universal_approximation_cybenko
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf_cont : ContinuousOn f (UnitCube n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (w : Fin N → EuclideanSpace ℝ (Fin n)) (b : Fin N → ℝ) (α : Fin N → ℝ),
      ∀ x ∈ UnitCube n,
        |f x - neuralNetFun σ N w b α x| < ε := by
  sorry

end

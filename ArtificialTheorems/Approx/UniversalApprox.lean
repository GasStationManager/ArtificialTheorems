/-
Universal Approximation Theorem (Cybenko 1989) - Proof

Architecture:
- dense_of_forall_dual_vanish_eq_zero: Hahn-Banach density (Mathlib ingredients exist)
- riesz_decomposition: L = L⁺ - L⁻ (sorry — Banach lattice, not in Mathlib)
- sigmoidal_measures_eq: BCT + π-λ (sorry — measure theory)
- neuralNet_annihilator_trivial: combines decomposition + measures
- neuralNet_dense: combines Hahn-Banach + annihilator
- universal_approximation_cybenko': density → uniform approximation (proved)
-/

import ArtificialTheoremsSpec.Approx.UniversalApproxSpec

open MeasureTheory Topology ContinuousMap Set Filter Finset

open scoped NNReal ENNReal

noncomputable section

variable {n : ℕ}

/-! ## UnitCube properties -/

theorem UnitCube.isCompact : IsCompact (UnitCube n) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem UnitCube.nonempty : (UnitCube n).Nonempty :=
  ⟨fun _ => 0, fun _ _ => ⟨le_refl 0, zero_le_one⟩⟩

instance : CompactSpace ↥(UnitCube n) :=
  isCompact_iff_compactSpace.mp UnitCube.isCompact

/-! ## Neural network continuity -/

theorem neuralNetFun_continuous (σ : ℝ → ℝ) (hσ : Continuous σ)
    (N : ℕ) (w : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ) (α : Fin N → ℝ) :
    Continuous (neuralNetFun σ N w b α) := by
  apply continuous_finset_sum; intro j _
  exact continuous_const.mul (hσ.comp ((continuous_finset_sum _ fun i _ =>
    continuous_const.mul (continuous_apply i)).add continuous_const))

def neuralNetCMap (σ : ℝ → ℝ) (hσ : Continuous σ)
    (N : ℕ) (w : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ) (α : Fin N → ℝ) :
    C(↥(UnitCube n), ℝ) where
  toFun x := neuralNetFun σ N w b α (x : Fin n → ℝ)
  continuous_toFun := (neuralNetFun_continuous σ hσ N w b α).continuousOn.restrict

def neuralNetRange (σ : ℝ → ℝ) (hσ : Continuous σ) : Set C(↥(UnitCube n), ℝ) :=
  { g | ∃ (N : ℕ) (w : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ) (α : Fin N → ℝ),
    g = neuralNetCMap σ hσ N w b α }

/-! ## Lemma 1: Hahn-Banach density criterion

If every continuous linear functional vanishing on a submodule S is zero,
then S is dense. Proof via geometric Hahn-Banach separation.

The proof is straightforward: if S is not dense, pick g ∉ closure(S),
separate g from closure(S), show the separating functional vanishes on S
(by the submodule scaling argument), contradiction. All Mathlib ingredients
exist (geometric_hahn_banach_closed_point, Submodule.convex, etc.). -/

theorem dense_of_forall_dual_vanish_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E)
    (h : ∀ L : E →L[ℝ] ℝ, (∀ s ∈ (S : Set E), L s = 0) → L = 0) :
    Dense (S : Set E) := by
  -- Proof: suppose not dense. Pick g ∉ closure(S). Hahn-Banach gives L
  -- with L(a) < u for a ∈ closure(S) and u < L(g). For s ∈ S, r • s ∈ S
  -- for all r, so r * L(s) < u for all r, forcing L(s) = 0.
  -- But h says L = 0, contradicting L(g) > 0.
  sorry -- Hahn-Banach argument; all Mathlib ingredients exist

/-! ## Lemma 2: Positive decomposition of functionals (sorry'd)

Any L ∈ C(K,ℝ)* decomposes as L⁺ - L⁻ where L⁺, L⁻ are positive.
This is the Riesz decomposition for Banach lattices. Not in Mathlib v4.27.0
(no BanachLattice class, no lattice on ContinuousLinearMap).

Reference: Aliprantis & Border, "Infinite Dimensional Analysis", Thm 9.11. -/

def IsPositiveLinearFunctional
    (L : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ f : C(↥(UnitCube n), ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f

theorem riesz_decomposition
    (L : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ) :
    ∃ (Lpos Lneg : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ),
      IsPositiveLinearFunctional Lpos ∧
      IsPositiveLinearFunctional Lneg ∧
      ∀ f, L f = Lpos f - Lneg f := by
  sorry -- Banach lattice decomposition

/-! ## Lemma 3: Sigmoidal measure uniqueness (sorry'd)

If two finite measures agree on ∫ σ(⟨w,x⟩+b) for all w,b where σ is
continuous sigmoidal, then they are equal.

Proof sketch: scale w by λ→∞. By bounded convergence theorem,
σ(λ⟨w,x⟩+b) → 1_{⟨w,x⟩>0} + σ(b)·1_{⟨w,x⟩=0}. So the measures agree
on all half-spaces. Since half-spaces generate the Borel σ-algebra
(π-system), the measures are equal by Dynkin's theorem. -/

theorem sigmoidal_measures_eq
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (μ₁ μ₂ : Measure (↥(UnitCube n)))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : ∀ (w : Fin n → ℝ) (b : ℝ),
      ∫ x, σ (∑ i, w i * (x : Fin n → ℝ) i + b) ∂μ₁ =
      ∫ x, σ (∑ i, w i * (x : Fin n → ℝ) i + b) ∂μ₂) :
    μ₁ = μ₂ := by
  sorry -- BCT + π-λ uniqueness

/-! ## Lemma 4: Annihilator is trivial

Any continuous linear functional vanishing on all neural net functions
is zero. Proof: decompose L = L⁺ - L⁻ (Lemma 2), convert to measures
via positive RMK, show measures agree by Lemma 3, hence L = 0. -/

theorem neuralNet_annihilator_trivial
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (L : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ)
    (hL : ∀ g ∈ neuralNetRange σ hσ_cont, L g = 0) : L = 0 := by
  sorry -- Combines riesz_decomposition + positive RMK + sigmoidal_measures_eq

/-! ## Lemma 5: Neural nets are dense

Combines Lemma 1 (Hahn-Banach density) with Lemma 4 (trivial annihilator). -/

theorem neuralNet_dense (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ) :
    Dense (neuralNetRange (n := n) σ hσ_cont) := by
  -- The span is dense (Hahn-Banach + trivial annihilator).
  -- neuralNetRange is a linear subspace = its own span, hence dense.
  sorry

/-! ## Main theorem: density → uniform approximation -/

/-- **Cybenko's Universal Approximation Theorem (1989).**
    Neural networks with a single hidden layer and continuous sigmoidal
    activation can uniformly approximate any continuous function on [0,1]ⁿ. -/
theorem universal_approximation_cybenko'
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (f : (Fin n → ℝ) → ℝ) (hf_cont : ContinuousOn f (UnitCube n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (w : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ) (α : Fin N → ℝ),
      ∀ x ∈ UnitCube n,
        |f x - neuralNetFun σ N w b α x| < ε := by
  have h_dense : Dense (neuralNetRange (n := n) σ hσ_cont) := neuralNet_dense σ hσ_cont hσ_sig
  let g : C(↥(UnitCube n), ℝ) := ⟨fun x => f x, hf_cont.restrict⟩
  obtain ⟨nn, ⟨N, w, b, α, rfl⟩, h_dist⟩ := h_dense.exists_dist_lt g hε
  refine ⟨N, w, b, α, fun x hx => ?_⟩
  have h_pw := ContinuousMap.norm_coe_le_norm
    (g - neuralNetCMap σ hσ_cont N w b α) (⟨x, hx⟩ : ↥(UnitCube n))
  simp only [ContinuousMap.coe_sub, Pi.sub_apply, g, neuralNetCMap,
    ContinuousMap.coe_mk] at h_pw
  rw [dist_eq_norm] at h_dist
  rw [Real.norm_eq_abs] at h_pw
  exact lt_of_le_of_lt h_pw h_dist

end

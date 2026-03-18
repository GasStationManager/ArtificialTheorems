/-
Universal Approximation Theorem (Cybenko 1989) - Proof

Architecture:
- dense_of_forall_dual_vanish_eq_zero: Hahn-Banach density (Mathlib ingredients exist)
- riesz_decomposition: L = L⁺ - L⁻ (sorry — Banach lattice, not in Mathlib)
- sigmoidal_measures_eq: BCT + π-λ (decomposed into sub-lemmas)
- neuralNet_annihilator_trivial: combines decomposition + measures (structured proof)
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
  rw [dense_iff_closure_eq]
  by_contra h_ne
  have ⟨g, hg⟩ : ∃ g, g ∉ closure (S : Set E) := by
    by_contra h_all; push_neg at h_all
    exact h_ne (Set.eq_univ_of_forall h_all)
  obtain ⟨L, u, hL_bd, hL_g⟩ :=
    geometric_hahn_banach_closed_point S.convex.closure isClosed_closure hg
  have hL_vanish : ∀ s ∈ (S : Set E), L s = 0 := by
    intro s hs
    by_contra hs_ne
    have bound : ∀ (r : ℝ), r * L s < u := by
      intro r
      have hmem : r • s ∈ closure (S : Set E) := subset_closure (S.smul_mem r hs)
      have := hL_bd _ hmem
      rwa [L.map_smul, smul_eq_mul] at this
    rcases lt_or_gt_of_ne hs_ne with hlt | hgt
    · have h1 := bound ((u + 1) / L s)
      rw [div_mul_cancel₀ _ (ne_of_lt hlt)] at h1
      linarith
    · have h1 := bound ((u + 1) / L s)
      rw [div_mul_cancel₀ _ (ne_of_gt hgt)] at h1
      linarith
  have hL_zero := h L hL_vanish
  have h0 := hL_bd 0 (subset_closure S.zero_mem)
  rw [hL_zero] at hL_g h0
  simp at hL_g h0
  linarith

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

/-! ## Lemma 3: Sigmoidal measure uniqueness

If two finite measures agree on ∫ σ(⟨w,x⟩+b) for all w,b where σ is
continuous sigmoidal, then they are equal.

Proof: scale w by λ→∞. By BCT, σ(λ⟨w,x⟩+b) → 1_{⟨w,x⟩>0} pointwise
(up to the hyperplane). So the measures agree on all open half-spaces.
Half-spaces form a π-system generating the Borel σ-algebra, so by the
π-λ theorem (uniqueness of extension), μ₁ = μ₂. -/

/-- Two finite measures agreeing on all open half-spaces are equal.
    Uses: open half-spaces form a π-system generating Borel σ-algebra,
    then apply π-λ uniqueness theorem. -/
theorem measures_eq_of_halfspaces
    (μ₁ μ₂ : Measure (↥(UnitCube n)))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : ∀ (w : Fin n → ℝ), μ₁ {x | 0 < ∑ i, w i * (x : Fin n → ℝ) i} =
                              μ₂ {x | 0 < ∑ i, w i * (x : Fin n → ℝ) i}) :
    μ₁ = μ₂ := by
  sorry -- π-system / Dynkin argument: half-spaces generate the Borel σ-algebra

/-- Scaling σ(λ⟨w,x⟩+b) as λ→∞ and applying BCT shows that two measures
    agreeing on all sigmoidal integrals agree on half-space measures. -/
theorem halfspaces_of_sigmoidal_integrals
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (μ₁ μ₂ : Measure (↥(UnitCube n)))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : ∀ (w : Fin n → ℝ) (b : ℝ),
      ∫ x, σ (∑ i, w i * (x : Fin n → ℝ) i + b) ∂μ₁ =
      ∫ x, σ (∑ i, w i * (x : Fin n → ℝ) i + b) ∂μ₂)
    (w : Fin n → ℝ) :
    μ₁ {x | 0 < ∑ i, w i * (x : Fin n → ℝ) i} =
    μ₂ {x | 0 < ∑ i, w i * (x : Fin n → ℝ) i} := by
  sorry -- BCT: scale w↦λw with λ→∞, σ(λ⟨w,x⟩) → indicator, integrals converge

theorem sigmoidal_measures_eq
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (μ₁ μ₂ : Measure (↥(UnitCube n)))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : ∀ (w : Fin n → ℝ) (b : ℝ),
      ∫ x, σ (∑ i, w i * (x : Fin n → ℝ) i + b) ∂μ₁ =
      ∫ x, σ (∑ i, w i * (x : Fin n → ℝ) i + b) ∂μ₂) :
    μ₁ = μ₂ :=
  measures_eq_of_halfspaces μ₁ μ₂
    (halfspaces_of_sigmoidal_integrals σ hσ_cont hσ_sig μ₁ μ₂ h)

/-! ## Lemma 4: Annihilator is trivial

Any continuous linear functional vanishing on all neural net functions
is zero. Proof: decompose L = L⁺ - L⁻ (Lemma 2), convert to measures
via positive RMK, show measures agree by Lemma 3, hence L = 0. -/

/-- Bridge: a positive linear functional on C(K,ℝ) (compact K) induces a
    finite Borel measure via the Riesz–Markov–Kakutani theorem, and
    integration against this measure recovers the functional. -/
theorem positive_functional_to_measure
    (Λ : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ) (hΛ : IsPositiveLinearFunctional Λ) :
    ∃ (μ : Measure ↥(UnitCube n)), IsFiniteMeasure μ ∧
      ∀ f : C(↥(UnitCube n), ℝ), Λ f = ∫ x, f x ∂μ := by
  sorry -- Bridge C(K,ℝ) →L[ℝ] ℝ to C_c(K,ℝ) →ₚ[ℝ] ℝ (compact ⟹ C = C_c), apply RMK

theorem neuralNet_annihilator_trivial
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (L : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ)
    (hL : ∀ g ∈ neuralNetRange σ hσ_cont, L g = 0) : L = 0 := by
  -- Step 1: Decompose L = Lpos - Lneg where both are positive functionals
  obtain ⟨Lpos, Lneg, hpos, hneg, hdecomp⟩ := riesz_decomposition L
  -- Step 2: Convert positive functionals to measures via RMK
  obtain ⟨μ₁, hfin₁, hint₁⟩ := positive_functional_to_measure Lpos hpos
  obtain ⟨μ₂, hfin₂, hint₂⟩ := positive_functional_to_measure Lneg hneg
  -- Step 3: L vanishes on neural nets ⟹ μ₁ and μ₂ agree on sigmoidal integrals
  have h_agree : ∀ (w : Fin n → ℝ) (b : ℝ),
      ∫ x, σ (∑ i, w i * (x : Fin n → ℝ) i + b) ∂μ₁ =
      ∫ x, σ (∑ i, w i * (x : Fin n → ℝ) i + b) ∂μ₂ := by
    intro w b
    -- Single neuron σ(⟨w,·⟩+b) is in the neural net range (N=1, α=1)
    have hmem : neuralNetCMap σ hσ_cont 1 (fun _ => w) (fun _ => b) (fun _ => 1) ∈
        neuralNetRange σ hσ_cont :=
      ⟨1, fun _ => w, fun _ => b, fun _ => 1, rfl⟩
    have hLzero := hL _ hmem
    -- L g = Lpos g - Lneg g = 0  ⟹  Lpos g = Lneg g  ⟹  ∫ g dμ₁ = ∫ g dμ₂
    -- The neuralNetCMap with N=1, α=1 evaluates to σ(⟨w,x⟩+b)
    -- So hint₁/hint₂ convert Lpos/Lneg values to integrals, and hdecomp + hLzero give equality
    let g := neuralNetCMap σ hσ_cont 1 (fun _ => w) (fun _ => b) (fun _ => 1)
    have h1 : Lpos g = ∫ x, g x ∂μ₁ := hint₁ g
    have h2 : Lneg g = ∫ x, g x ∂μ₂ := hint₂ g
    have h3 : Lpos g = Lneg g := by linarith [hdecomp g]
    -- Need: ∫ g dμᵢ = ∫ σ(⟨w,·⟩+b) dμᵢ (they're the same function)
    have hg_eq : ∀ x : ↥(UnitCube n), g x = σ (∑ i, w i * (x : Fin n → ℝ) i + b) := by
      intro x; simp [g, neuralNetCMap, neuralNetFun]
    rw [show (∫ x, σ (∑ i, w i * (x : Fin n → ℝ) i + b) ∂μ₁) =
            ∫ x, g x ∂μ₁ from by congr 1; ext x; exact (hg_eq x).symm,
        show (∫ x, σ (∑ i, w i * (x : Fin n → ℝ) i + b) ∂μ₂) =
            ∫ x, g x ∂μ₂ from by congr 1; ext x; exact (hg_eq x).symm]
    linarith
  -- Step 4: By sigmoidal_measures_eq, μ₁ = μ₂
  have hμeq : μ₁ = μ₂ := sigmoidal_measures_eq σ hσ_cont hσ_sig μ₁ μ₂ h_agree
  -- Step 5: L f = ∫f dμ₁ - ∫f dμ₂ = 0 for all f
  ext f
  simp only [ContinuousLinearMap.zero_apply]
  rw [hdecomp f, hint₁ f, hint₂ f, hμeq, sub_self]

/-! ## Lemma 5: Neural nets are dense

Combines Lemma 1 (Hahn-Banach density) with Lemma 4 (trivial annihilator). -/

/-- neuralNetRange is a submodule: it contains 0, and is closed under
    addition (concatenate networks) and scalar multiplication (scale coefficients). -/
def neuralNetSubmodule (σ : ℝ → ℝ) (hσ : Continuous σ) :
    Submodule ℝ C(↥(UnitCube n), ℝ) where
  carrier := neuralNetRange σ hσ
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, by
    ext x; simp [neuralNetCMap, neuralNetFun]⟩
  add_mem' := by
    rintro _ _ ⟨N₁, w₁, b₁, α₁, rfl⟩ ⟨N₂, w₂, b₂, α₂, rfl⟩
    exact ⟨N₁ + N₂, Fin.append w₁ w₂, Fin.append b₁ b₂, Fin.append α₁ α₂, by
      ext x; simp only [neuralNetCMap, neuralNetFun, ContinuousMap.coe_mk,
        ContinuousMap.coe_add, Pi.add_apply]
      rw [Fin.sum_univ_add]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
        simp [Fin.append]⟩
  smul_mem' := by
    rintro r _ ⟨N, w, b, α, rfl⟩
    exact ⟨N, w, b, fun j => r * α j, by
      ext x; simp only [neuralNetCMap, neuralNetFun, ContinuousMap.coe_mk,
        ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]; congr 1; ext j; ring⟩

theorem neuralNet_dense (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ) :
    Dense (neuralNetRange (n := n) σ hσ_cont) := by
  have : (neuralNetRange σ hσ_cont : Set C(↥(UnitCube n), ℝ)) =
      ↑(neuralNetSubmodule σ hσ_cont : Submodule ℝ C(↥(UnitCube n), ℝ)) := by
    ext; simp [neuralNetSubmodule, neuralNetRange]
  rw [this]
  exact dense_of_forall_dual_vanish_eq_zero _ (fun L hL =>
    neuralNet_annihilator_trivial σ hσ_cont hσ_sig L (fun g hg => hL g hg))

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

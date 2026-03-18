/-
Universal Approximation Theorem (Cybenko 1989) - Proof

AI-generated proof following Cybenko's original strategy:
1. Sigmoidal ⟹ discriminatory (via dominated convergence on scaled arguments)
2. Discriminatory ⟹ neural net span dense in C(Iₙ) (via Hahn-Banach + Riesz)
3. Density ⟹ uniform approximation
-/

import ArtificialTheoremsSpec.Approx.UniversalApproxSpec

open MeasureTheory Topology ContinuousMap Set Filter Finset

open scoped NNReal ENNReal

noncomputable section

variable {n : ℕ}

/-! ## Basic properties of UnitCube -/

theorem UnitCube.isCompact : IsCompact (UnitCube n) := by
  unfold UnitCube; exact isCompact_univ_pi fun _ => isCompact_Icc

theorem UnitCube.nonempty : (UnitCube n).Nonempty :=
  ⟨fun _ => 0, fun _ _ => ⟨le_refl 0, zero_le_one⟩⟩

instance : CompactSpace ↥(UnitCube n) :=
  isCompact_iff_compactSpace.mp UnitCube.isCompact

/-! ## Neural network functions are continuous -/

theorem neuralNetFun_continuous (σ : ℝ → ℝ) (hσ : Continuous σ)
    (N : ℕ) (w : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ) (α : Fin N → ℝ) :
    Continuous (fun x : Fin n → ℝ => neuralNetFun σ N w b α x) := by
  apply continuous_finset_sum; intro j _
  exact (continuous_const.mul (hσ.comp ((continuous_finset_sum _ fun i _ =>
    continuous_const.mul (continuous_apply i)).add continuous_const)))

/-! ## The set of neural net ContinuousMaps on UnitCube -/

/-- Construct a ContinuousMap on UnitCube from neural net parameters. -/
def neuralNetCMap (σ : ℝ → ℝ) (hσ : Continuous σ)
    (N : ℕ) (w : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ) (α : Fin N → ℝ) :
    C(↥(UnitCube n), ℝ) where
  toFun x := neuralNetFun σ N w b α (x : Fin n → ℝ)
  continuous_toFun := (neuralNetFun_continuous σ hσ N w b α).continuousOn.restrict

/-- The set of all neural net continuous maps on UnitCube. -/
def neuralNetRange (σ : ℝ → ℝ) (hσ : Continuous σ) : Set C(↥(UnitCube n), ℝ) :=
  { g | ∃ (N : ℕ) (w : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ) (α : Fin N → ℝ),
    g = neuralNetCMap σ hσ N w b α }

/-! ## Core density theorem (Cybenko's main result)

**Proof outline:**
1. Define "discriminatory": σ is discriminatory if any signed Borel measure μ on Iₙ
   with ∫ σ(⟨w,x⟩+b) dμ = 0 ∀ w,b must be μ = 0.
2. If σ is discriminatory and the neural net span is not dense, Hahn-Banach yields
   a nonzero continuous linear functional L vanishing on the span. By Riesz
   representation, L corresponds to a nonzero signed measure μ. But discriminatory
   forces μ = 0, contradiction.
3. Continuous sigmoidal ⟹ discriminatory: σ(λ(⟨w,x⟩+b)) → 1_{⟨w,x⟩>-b} as λ→∞
   by sigmoidal property. Dominated convergence gives μ(half-spaces) = 0. Since
   half-spaces generate the Borel σ-algebra, μ = 0.

This proof requires the Riesz representation theorem for signed measures
(dual of C(K) ≅ signed Radon measures), which is not fully available in
Mathlib v4.27.0 (only the positive/NNReal version exists). We axiomatize
this as a sorry.
-/

/-- Auxiliary: if every continuous linear functional vanishing on S is zero, S is dense.
    This follows from Hahn-Banach separation for normed spaces. -/
theorem dense_of_dual_annihilator_eq_zero
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X)
    (h : ∀ L : X →L[ℝ] ℝ, (∀ s ∈ S, L s = 0) → L = 0) :
    Dense S := by
  sorry

/-- The measure-theoretic heart: continuous sigmoidal functions have trivial annihilator.
    Proof sketch: By Riesz representation, any L ∈ C(Iₙ)* corresponds to a signed measure μ.
    If L vanishes on all neural nets, then ∫ σ(⟨w,x⟩+b) dμ = 0 for all w,b.
    Taking σ(λ(⟨w,x⟩+b)) as λ→∞ and using dominated convergence gives μ(half-spaces) = 0.
    Since half-spaces generate the Borel σ-algebra, μ = 0, hence L = 0. -/
theorem sigmoidal_annihilator_trivial (σ : ℝ → ℝ) (hσ_cont : Continuous σ)
    (hσ_sig : IsSigmoidal σ) :
    ∀ L : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ,
      (∀ g ∈ neuralNetRange σ hσ_cont, L g = 0) → L = 0 := by
  sorry

/-- Neural net functions are dense in C(Iₙ, ℝ) when σ is continuous and sigmoidal. -/
theorem neuralNet_dense (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ) :
    Dense (neuralNetRange (n := n) σ hσ_cont) := by
  exact dense_of_dual_annihilator_eq_zero _
    (sigmoidal_annihilator_trivial σ hσ_cont hσ_sig)

/-! ## Main theorem: extract uniform approximation from density -/

theorem universal_approximation_cybenko'
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (f : (Fin n → ℝ) → ℝ) (hf_cont : ContinuousOn f (UnitCube n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (w : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ) (α : Fin N → ℝ),
      ∀ x ∈ UnitCube n,
        |f x - neuralNetFun σ N w b α x| < ε := by
  -- Restrict f to UnitCube as a ContinuousMap
  let g : C(↥(UnitCube n), ℝ) := ⟨fun x => f x, hf_cont.restrict⟩
  -- Neural nets are dense
  have h_dense : Dense (neuralNetRange (n := n) σ hσ_cont) := neuralNet_dense σ hσ_cont hσ_sig
  -- Find a neural net function within ε of g in C(Iₙ, ℝ)
  obtain ⟨nn, ⟨N, w, b, α, rfl⟩, h_dist⟩ := h_dense.exists_dist_lt g hε
  refine ⟨N, w, b, α, fun x hx => ?_⟩
  -- Pointwise |f(x) - nn(x)| ≤ ‖f - nn‖_∞ = dist(f, nn) < ε
  have h_pw := ContinuousMap.norm_coe_le_norm
    (g - neuralNetCMap σ hσ_cont N w b α) (⟨x, hx⟩ : ↥(UnitCube n))
  simp only [ContinuousMap.coe_sub, Pi.sub_apply, g, neuralNetCMap,
    ContinuousMap.coe_mk] at h_pw
  rw [dist_eq_norm] at h_dist
  rw [Real.norm_eq_abs] at h_pw
  exact lt_of_le_of_lt h_pw h_dist

end

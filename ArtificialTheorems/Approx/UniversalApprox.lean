/-
Universal Approximation Theorem (Cybenko 1989) - Proof

Architecture:
- dense_of_forall_dual_vanish_eq_zero: Hahn-Banach density (Mathlib ingredients exist)
- HasJordanDecomposition: L = L⁺ - L⁻ (assumed as premise — classical, not in Mathlib)
- sigmoidal_measures_eq: BCT + π-λ (decomposed into sub-lemmas)
- neuralNet_annihilator_trivial: combines decomposition + measures (structured proof)
- neuralNet_dense: combines Hahn-Banach + annihilator
- universal_approximation_cybenko: density → uniform approximation (proved)
-/

import Mathlib

open MeasureTheory Topology ContinuousMap Set Filter Finset

open scoped NNReal ENNReal

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

/-! ## Lemma 2: Jordan decomposition (HasJordanDecomposition)

Every continuous linear functional on C(K,ℝ) for compact Hausdorff K is the
difference of two positive continuous linear functionals.

This classical result (Rudin RCA Thms 6.19 + 6.12; Aliprantis & Border
Thms 9.11, 9.14, 8.48; Conway §V.8; Folland Thm 7.17) is not in Mathlib
v4.27.0 (no BanachLattice class, no signed RMK). We assume it as a premise.
See the spec file for additional documentation. -/

def IsPositiveLinearFunctional
    (L : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ f : C(↥(UnitCube n), ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f

/-- Jordan decomposition of continuous linear functionals on C(Iₙ,ℝ). -/
def HasJordanDecomposition (n : ℕ) : Prop :=
  ∀ (L : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ),
    ∃ (Lpos Lneg : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ),
      IsPositiveLinearFunctional Lpos ∧
      IsPositiveLinearFunctional Lneg ∧
      ∀ f, L f = Lpos f - Lneg f


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
    (h : ∀ (w : Fin n → ℝ) (b : ℝ),
      μ₁ {x | 0 < ∑ i, w i * (x : Fin n → ℝ) i + b} =
      μ₂ {x | 0 < ∑ i, w i * (x : Fin n → ℝ) i + b}) :
    μ₁ = μ₂ := by
  -- Strategy: push forward to ℝ via each linear functional φ_w, show pushforwards
  -- agree via ext_of_generate_finite with the Ioi π-system, then lift back.
  -- Step 0: Total mass agrees (w = 0, b = 1 gives univ)
  have h_univ : μ₁ Set.univ = μ₂ Set.univ := by
    have := h 0 1
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, zero_lt_one,
      Set.setOf_true] at this
    exact this
  -- Step 1: For each w, the 1-d pushforward measures on ℝ agree
  set φ : (Fin n → ℝ) → ↥(UnitCube n) → ℝ :=
    fun w x => ∑ i, w i * (x : Fin n → ℝ) i with hφ_def
  have hφ_meas : ∀ w, Measurable (φ w) :=
    fun w => (continuous_finset_sum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).comp continuous_subtype_val)).measurable
  have h_map_eq : ∀ w : Fin n → ℝ, μ₁.map (φ w) = μ₂.map (φ w) := by
    intro w
    apply ext_of_generate_finite (range Set.Ioi)
      (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ))
      isPiSystem_Ioi
    · rintro s ⟨r, rfl⟩
      rw [Measure.map_apply (hφ_meas w) measurableSet_Ioi,
          Measure.map_apply (hφ_meas w) measurableSet_Ioi]
      have key := h w (-r)
      have : φ w ⁻¹' Set.Ioi r =
          {x : ↥(UnitCube n) | 0 < ∑ i, w i * (x : Fin n → ℝ) i + -r} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq, φ]
        constructor
        · intro h; linarith
        · intro h; linarith
      simp only [this]; exact key
    · rw [Measure.map_apply (hφ_meas w) MeasurableSet.univ,
          Measure.map_apply (hφ_meas w) MeasurableSet.univ]
      simp [h_univ]
  -- Step 2: Push both measures to (Fin n → ℝ) via Subtype.val, show charFunDual agrees.
  set ι : ↥(UnitCube n) → (Fin n → ℝ) := Subtype.val with hι_def
  have hι_me : MeasurableEmbedding ι :=
    MeasurableEmbedding.subtype_coe ((measurableSet_pi Set.countable_univ |>.mpr (Or.inl (fun i _ => measurableSet_Icc))))
  set ν₁ := μ₁.map ι with hν₁_def
  set ν₂ := μ₂.map ι with hν₂_def
  -- Any continuous linear functional on (Fin n → ℝ) composes with ι to give φ w
  have h_decomp : ∀ (L : (Fin n → ℝ) →L[ℝ] ℝ),
      (L ∘ ι) = φ (fun i => L (Pi.single i 1)) := by
    intro L; ext x; simp only [Function.comp, φ]
    have key : ∀ (v : Fin n → ℝ), L v = ∑ i : Fin n, v i * L (Pi.single i 1) := by
      intro v
      have hv : v = ∑ i : Fin n, v i • (Pi.single i 1 : Fin n → ℝ) := by
        ext j; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']
      conv_lhs => rw [hv]
      rw [map_sum]; congr 1; ext i
      rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [key]; congr 1; ext i; ring
  -- ν₁.map L = ν₂.map L for all continuous linear L
  have h_map_L : ∀ (L : (Fin n → ℝ) →L[ℝ] ℝ), ν₁.map L = ν₂.map L := by
    intro L
    have h1 : ν₁.map L = μ₁.map (L ∘ ι) := by
      rw [hν₁_def, Measure.map_map L.measurable hι_me.measurable]
    have h2 : ν₂.map L = μ₂.map (L ∘ ι) := by
      rw [hν₂_def, Measure.map_map L.measurable hι_me.measurable]
    rw [h1, h2, h_decomp L]
    exact h_map_eq _
  -- charFunDual ν₁ = charFunDual ν₂
  have hcf : charFunDual ν₁ = charFunDual ν₂ := by
    ext L
    rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
    congr 1
    exact h_map_L L
  -- By ext_of_charFunDual, ν₁ = ν₂
  have hν_eq : ν₁ = ν₂ := Measure.ext_of_charFunDual hcf
  -- Since ι is a measurable embedding, μ₁ = μ₂
  ext t ht
  have h1 : μ₁ t = ν₁ (ι '' t) := by
    rw [hν₁_def, hι_me.map_apply]; congr 1
    exact (Set.preimage_image_eq t Subtype.val_injective).symm
  have h2 : μ₂ t = ν₂ (ι '' t) := by
    rw [hν₂_def, hι_me.map_apply]; congr 1
    exact (Set.preimage_image_eq t Subtype.val_injective).symm
  rw [h1, h2, hν_eq]

/-- Scaling σ(λ⟨w,x⟩+b) as λ→∞ and applying BCT shows that two measures
    agreeing on all sigmoidal integrals agree on affine half-space measures. -/
theorem halfspaces_of_sigmoidal_integrals
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (μ₁ μ₂ : Measure (↥(UnitCube n)))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : ∀ (w : Fin n → ℝ) (b : ℝ),
      ∫ x, σ (∑ i, w i * (x : Fin n → ℝ) i + b) ∂μ₁ =
      ∫ x, σ (∑ i, w i * (x : Fin n → ℝ) i + b) ∂μ₂)
    (w : Fin n → ℝ) (a : ℝ) :
    μ₁ {x | 0 < ∑ i, w i * (x : Fin n → ℝ) i + a} =
    μ₂ {x | 0 < ∑ i, w i * (x : Fin n → ℝ) i + a} := by
  -- For each k, h (fun i => ↑k * w i) 0 gives ∫ σ(k⟨w,x⟩) dμ₁ = ∫ σ(k⟨w,x⟩) dμ₂
  -- As k→∞, σ(k·t)→1 for t>0, σ(k·t)→0 for t<0, by IsSigmoidal.
  -- σ is bounded (continuous + limits at ±∞), so BCT applies.
  -- The limit integral equals the measure of {⟨w,x⟩ > 0} (up to null hyperplane).
  -- Since limits of equal sequences are equal, μ₁{⟨w,x⟩>0} = μ₂{⟨w,x⟩>0}.
  --
  set ip := fun x : ↥(UnitCube n) => ∑ i, w i * (x : Fin n → ℝ) i + a with hip
  -- Sub-lemma 1: σ is bounded
  have hσ_bdd : ∃ C : ℝ, ∀ t, ‖σ t‖ ≤ C := by
    -- σ → 1 at +∞ and σ → 0 at -∞, so bounded outside [-N,N].
    -- σ continuous on compact [-N,N], so bounded there. Max of all bounds works.
    -- Get bound at +∞: ∃ N₁, ∀ t ≥ N₁, |σ(t)| < 2
    have h1 : ∀ᶠ t in atTop, ‖σ t‖ < 2 := by
      have := hσ_sig.1.norm; rw [show ‖(1:ℝ)‖ = 1 from norm_one] at this
      exact (this.eventually (gt_mem_nhds (by norm_num : (1:ℝ) < 2))).mono fun t ht => ht
    -- Get bound at -∞: ∃ N₂, ∀ t ≤ N₂, |σ(t)| < 1
    have h2 : ∀ᶠ t in atBot, ‖σ t‖ < 1 := by
      have := hσ_sig.2.norm; rw [show ‖(0:ℝ)‖ = 0 from norm_zero] at this
      exact (this.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))).mono fun t ht => ht
    rw [Filter.eventually_atTop] at h1; rw [Filter.eventually_atBot] at h2
    obtain ⟨N₁, hN₁⟩ := h1; obtain ⟨N₂, hN₂⟩ := h2
    -- On [N₂-1, N₁+1], σ is continuous hence bounded. Outside, use tail bounds.
    obtain ⟨M, hM⟩ := (isCompact_Icc.image hσ_cont.norm).isBounded.subset_closedBall 0
    use max M 2
    intro t
    by_cases h_hi : N₁ ≤ t
    · exact le_max_of_le_right (le_of_lt (hN₁ t h_hi))
    · by_cases h_lo : t ≤ N₂
      · exact le_max_of_le_right (le_of_lt (lt_of_lt_of_le (hN₂ t h_lo) one_le_two))
      · push_neg at h_hi h_lo
        have ht_mem : t ∈ Set.Icc (N₂ - 1) (N₁ + 1) :=
          ⟨by linarith, by linarith⟩
        have : ‖σ t‖ ∈ (fun x => ‖σ x‖) '' Set.Icc (N₂ - 1) (N₁ + 1) :=
          Set.mem_image_of_mem _ ht_mem
        have hmem := hM this
        rw [Metric.mem_closedBall, Real.dist_eq] at hmem
        rw [sub_zero] at hmem; exact le_max_of_le_left (le_trans (le_abs_self _) hmem)
    -- Sub-lemma 2: pointwise convergence σ(k·t) → indicator
  have h_pw : ∀ t : ℝ, t ≠ 0 →
      Tendsto (fun k : ℕ => σ (↑k * t)) atTop (𝓝 (if 0 < t then 1 else 0)) := by
    intro t ht
    rcases lt_or_gt_of_ne ht with ht_neg | ht_pos
    · simp [not_lt.mpr (le_of_lt ht_neg)]
      have : Tendsto (fun k : ℕ => (↑k : ℝ) * t) atTop atBot :=
        tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg' ht_neg
      exact hσ_sig.2.comp this
    · simp [ht_pos]
      have : Tendsto (fun k : ℕ => (↑k : ℝ) * t) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const' ht_pos
      exact hσ_sig.1.comp this
  -- Sub-lemma 3: Apply BCT to derive integral identities
  -- For any b, scaling w by λ→∞ in σ(λ⟨w,x⟩+b) gives:
  --   μᵢ{ip>0} + σ(b)·μᵢ{ip=0} is the same for i=1,2
  have h_bct : ∀ b : ℝ,
      (μ₁ {x | 0 < ip x}).toReal + σ b * (μ₁ {x | ip x = 0}).toReal =
      (μ₂ {x | 0 < ip x}).toReal + σ b * (μ₂ {x | ip x = 0}).toReal := by
    intro b
    set F : ℕ → ↥(UnitCube n) → ℝ := fun k x => σ (↑k * ip x + b)
    set f_lim : ↥(UnitCube n) → ℝ := fun x =>
        if 0 < ip x then 1 else if ip x = 0 then σ b else 0
    have h_eq_k : ∀ k : ℕ, ∫ x, F k x ∂μ₁ = ∫ x, F k x ∂μ₂ := by
      intro k
      have := h (fun i => ↑k * w i) (↑k * a + b)
      convert this using 2
      · ext x
        simp [F, ip, mul_add, Finset.mul_sum, add_assoc, add_assoc, add_comm, mul_assoc]
      · ext x
        simp [F, ip, mul_add, Finset.mul_sum, add_assoc, add_assoc, add_comm, mul_assoc]
    obtain ⟨C, hC⟩ := hσ_bdd
    have hcont_ip : Continuous ip := by
      change Continuous (fun x : ↥(UnitCube n) => ∑ i, w i * (x : Fin n → ℝ) i + a)
      exact
        (continuous_finset_sum _ fun i _ =>
          continuous_const.mul
            ((continuous_apply i : Continuous fun x : Fin n → ℝ => x i).comp
              continuous_subtype_val)).add continuous_const
    have hmeas_pos : MeasurableSet {x | 0 < ip x} :=
      measurableSet_lt measurable_const hcont_ip.measurable
    have hmeas_zero : MeasurableSet {x | ip x = 0} :=
      measurableSet_eq_fun hcont_ip.measurable measurable_const
    have hF_meas : ∀ k : ℕ, Continuous (F k) := by
      intro k
      change Continuous (fun x : ↥(UnitCube n) => σ (↑k * ip x + b))
      exact hσ_cont.comp ((continuous_const.mul hcont_ip).add continuous_const)
    have hF_bound₁ : ∀ k : ℕ, ∀ᵐ x ∂μ₁, ‖F k x‖ ≤ (fun _ : ↥(UnitCube n) => C) x := by
      intro k
      exact Filter.Eventually.of_forall fun x => by
        change ‖σ (↑k * ip x + b)‖ ≤ C
        exact hC (↑k * ip x + b)
    have hF_bound₂ : ∀ k : ℕ, ∀ᵐ x ∂μ₂, ‖F k x‖ ≤ (fun _ : ↥(UnitCube n) => C) x := by
      intro k
      exact Filter.Eventually.of_forall fun x => by
        change ‖σ (↑k * ip x + b)‖ ≤ C
        exact hC (↑k * ip x + b)
    have hF_lim : ∀ x : ↥(UnitCube n), Tendsto (fun k : ℕ => F k x) atTop (𝓝 (f_lim x)) := by
      intro x
      by_cases hx_pos : 0 < ip x
      · have harg : Tendsto (fun k : ℕ => (↑k : ℝ) * ip x + b) atTop atTop :=
          Filter.Tendsto.atTop_add
            (tendsto_natCast_atTop_atTop.atTop_mul_const' hx_pos) tendsto_const_nhds
        have hσ_lim : Tendsto (fun k : ℕ => σ ((↑k : ℝ) * ip x + b)) atTop (𝓝 1) :=
          hσ_sig.1.comp harg
        change Tendsto (fun k : ℕ => σ ((↑k : ℝ) * ip x + b)) atTop (𝓝 (f_lim x))
        simpa [f_lim, hx_pos, hx_pos.ne'] using hσ_lim
      · by_cases hx_zero : ip x = 0
        · change Tendsto (fun k : ℕ => σ ((↑k : ℝ) * ip x + b)) atTop (𝓝 (f_lim x))
          simpa [f_lim, hx_pos, hx_zero] using
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => σ b) atTop (𝓝 (σ b)))
        · have hx_neg : ip x < 0 := lt_of_le_of_ne (le_of_not_gt hx_pos) hx_zero
          have harg : Tendsto (fun k : ℕ => (↑k : ℝ) * ip x + b) atTop atBot :=
            Filter.Tendsto.atBot_add
              (tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg' hx_neg) tendsto_const_nhds
          have hσ_lim : Tendsto (fun k : ℕ => σ ((↑k : ℝ) * ip x + b)) atTop (𝓝 0) :=
            hσ_sig.2.comp harg
          change Tendsto (fun k : ℕ => σ ((↑k : ℝ) * ip x + b)) atTop (𝓝 (f_lim x))
          simpa [f_lim, hx_pos, hx_zero] using hσ_lim
    have hlim₁ :
        Tendsto (fun k : ℕ => ∫ x, F k x ∂μ₁) atTop (𝓝 <| ∫ x, f_lim x ∂μ₁) :=
      tendsto_integral_of_dominated_convergence (μ := μ₁) (bound := fun _ => C)
        (fun k => (hF_meas k).aestronglyMeasurable)
        (integrable_const C) hF_bound₁ (ae_of_all _ hF_lim)
    have hlim₂ :
        Tendsto (fun k : ℕ => ∫ x, F k x ∂μ₂) atTop (𝓝 <| ∫ x, f_lim x ∂μ₂) :=
      tendsto_integral_of_dominated_convergence (μ := μ₂) (bound := fun _ => C)
        (fun k => (hF_meas k).aestronglyMeasurable)
        (integrable_const C) hF_bound₂ (ae_of_all _ hF_lim)
    have h_int_eq : ∫ x, f_lim x ∂μ₁ = ∫ x, f_lim x ∂μ₂ := by
      have hlim₂' :
          Tendsto (fun k : ℕ => ∫ x, F k x ∂μ₁) atTop (𝓝 <| ∫ x, f_lim x ∂μ₂) := by
        exact hlim₂.congr' (Filter.Eventually.of_forall fun k => (h_eq_k k).symm)
      exact tendsto_nhds_unique hlim₁ hlim₂'
    have h_int_formula (μ : Measure ↥(UnitCube n)) [IsFiniteMeasure μ] :
        ∫ x, f_lim x ∂μ =
          (μ {x | 0 < ip x}).toReal + σ b * (μ {x | ip x = 0}).toReal := by
      have hpos_int : Integrable (Set.indicator {x | 0 < ip x} (fun _ => (1 : ℝ))) μ :=
        (integrable_const 1).indicator hmeas_pos
      have hzero_int : Integrable (Set.indicator {x | ip x = 0} (fun _ => σ b)) μ :=
        (integrable_const (σ b)).indicator hmeas_zero
      have hf_lim_eq :
          f_lim =
            fun x =>
              Set.indicator {x | 0 < ip x} (fun _ => (1 : ℝ)) x +
                Set.indicator {x | ip x = 0} (fun _ => σ b) x := by
        funext x
        by_cases hx_pos : 0 < ip x
        · simp [f_lim, hx_pos, hx_pos.ne']
        · by_cases hx_zero : ip x = 0
          · simp [f_lim, hx_pos, hx_zero]
          · simp [f_lim, hx_pos, hx_zero]
      calc
        ∫ x, f_lim x ∂μ
            = ∫ x,
                Set.indicator {x | 0 < ip x} (fun _ => (1 : ℝ)) x +
                  Set.indicator {x | ip x = 0} (fun _ => σ b) x ∂μ := by
              rw [hf_lim_eq]
        _ = ∫ x, Set.indicator {x | 0 < ip x} (fun _ => (1 : ℝ)) x ∂μ +
              ∫ x, Set.indicator {x | ip x = 0} (fun _ => σ b) x ∂μ := by
              rw [integral_add hpos_int hzero_int]
        _ = ∫ x in {x | 0 < ip x}, (1 : ℝ) ∂μ + ∫ x in {x | ip x = 0}, σ b ∂μ := by
              rw [integral_indicator hmeas_pos, integral_indicator hmeas_zero]
        _ = (μ {x | 0 < ip x}).toReal + σ b * (μ {x | ip x = 0}).toReal := by
              rw [setIntegral_one_eq_measureReal, setIntegral_const]
              simp [measureReal_def, smul_eq_mul, mul_comm]
    calc
      (μ₁ {x | 0 < ip x}).toReal + σ b * (μ₁ {x | ip x = 0}).toReal = ∫ x, f_lim x ∂μ₁ := by
        symm
        exact h_int_formula μ₁
      _ = ∫ x, f_lim x ∂μ₂ := h_int_eq
      _ = (μ₂ {x | 0 < ip x}).toReal + σ b * (μ₂ {x | ip x = 0}).toReal := h_int_formula μ₂
  -- Sub-lemma 4: Algebraic conclusion
  -- h_bct for varying b gives: d_pos + σ(b) · d_zero = 0 for all b.
  -- Since σ is not constant (limits 0 and 1), d_zero = 0, hence d_pos = 0.
  set d_pos := (μ₁ {x | 0 < ip x}).toReal - (μ₂ {x | 0 < ip x}).toReal
  set d_zero := (μ₁ {x | ip x = 0}).toReal - (μ₂ {x | ip x = 0}).toReal
  have h_eq_all : ∀ b : ℝ, d_pos + σ b * d_zero = 0 := by
    intro b; have := h_bct b; simp [d_pos, d_zero]; linarith
  have hd_zero : d_zero = 0 := by
    by_contra hne
    -- σ(b) = -d_pos / d_zero for all b, so σ is constant
    have hconst : ∀ b : ℝ, σ b = -d_pos / d_zero := by
      intro b; have := h_eq_all b
      field_simp at this ⊢; linarith
    -- But σ → 1 at +∞ and σ → 0 at -∞, contradiction
    have h1 : σ 0 = -d_pos / d_zero := hconst 0
    have h2' : σ 0 = -d_pos / d_zero := hconst 0
    have hlim1 := tendsto_nhds_unique hσ_sig.1 (tendsto_const_nhds (x := -d_pos / d_zero) |>.congr (fun n => (hconst n).symm))
    have hlim2 := tendsto_nhds_unique hσ_sig.2 (tendsto_const_nhds (x := -d_pos / d_zero) |>.congr (fun n => (hconst n).symm))
    linarith
  have hd_pos : d_pos = 0 := by have := h_eq_all 0; simp [hd_zero] at this; exact this
  -- Convert from toReal equality to ENNReal equality
  have hfin₁ : (μ₁ {x | 0 < ip x}) ≠ ⊤ := (measure_ne_top μ₁ _)
  have hfin₂ : (μ₂ {x | 0 < ip x}) ≠ ⊤ := (measure_ne_top μ₂ _)
  have htr : (μ₁ {x | 0 < ip x}).toReal = (μ₂ {x | 0 < ip x}).toReal := by
    simp [d_pos] at hd_pos; linarith
  rwa [ENNReal.toReal_eq_toReal_iff' hfin₁ hfin₂] at htr
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
  -- Bridge C(K,ℝ) →L[ℝ] ℝ to C_c(K,ℝ) →ₚ[ℝ] ℝ (compact ⟹ C = C_c), apply RMK
  -- Define the lifting from C_c to C: just forget compact support
  let toC : CompactlySupportedContinuousMap ↥(UnitCube n) ℝ →ₗ[ℝ]
            C(↥(UnitCube n), ℝ) :=
    { toFun := fun f => f.toContinuousMap
      map_add' := fun f g => rfl
      map_smul' := fun r f => rfl }
  -- Compose to get a linear map on C_c
  let Λ_lin := Λ.toLinearMap.comp toC
  -- It's positive because Λ is positive
  let Λ_cc : CompactlySupportedContinuousMap ↥(UnitCube n) ℝ →ₚ[ℝ] ℝ :=
    PositiveLinearMap.mk₀ Λ_lin (by
      intro f hf
      exact hΛ f.toContinuousMap (fun x => hf x))
  refine ⟨RealRMK.rieszMeasure Λ_cc, inferInstance, fun f => ?_⟩
  -- Use RMK integral theorem
  let f_cc : CompactlySupportedContinuousMap ↥(UnitCube n) ℝ :=
    ⟨f, HasCompactSupport.of_compactSpace f⟩
  have h := RealRMK.integral_rieszMeasure Λ_cc f_cc
  -- h : ∫ x, f_cc x ∂(rieszMeasure Λ_cc) = Λ_cc f_cc
  -- Λ_cc f_cc = Λ f by definition
  -- ∫ f_cc = ∫ f because they're the same function
  exact h.symm

theorem neuralNet_annihilator_trivial
    (hJD : HasJordanDecomposition n)
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (L : C(↥(UnitCube n), ℝ) →L[ℝ] ℝ)
    (hL : ∀ g ∈ neuralNetRange σ hσ_cont, L g = 0) : L = 0 := by
  -- Step 1: Decompose L = Lpos - Lneg where both are positive functionals
  obtain ⟨Lpos, Lneg, hpos, hneg, hdecomp⟩ := hJD L
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

theorem neuralNet_dense (hJD : HasJordanDecomposition n)
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ) :
    Dense (neuralNetRange (n := n) σ hσ_cont) := by
  have : (neuralNetRange σ hσ_cont : Set C(↥(UnitCube n), ℝ)) =
      ↑(neuralNetSubmodule σ hσ_cont : Submodule ℝ C(↥(UnitCube n), ℝ)) := by
    ext; simp [neuralNetSubmodule, neuralNetRange]
  rw [this]
  exact dense_of_forall_dual_vanish_eq_zero _ (fun L hL =>
    neuralNet_annihilator_trivial hJD σ hσ_cont hσ_sig L (fun g hg => hL g hg))

/-! ## Main theorem: density → uniform approximation -/

/-- **Cybenko's Universal Approximation Theorem (1989).**
    Neural networks with a single hidden layer and continuous sigmoidal
    activation can uniformly approximate any continuous function on [0,1]ⁿ. -/
theorem universal_approximation_cybenko
    (hJD : HasJordanDecomposition n)
    (σ : ℝ → ℝ) (hσ_cont : Continuous σ) (hσ_sig : IsSigmoidal σ)
    (f : (Fin n → ℝ) → ℝ) (hf_cont : ContinuousOn f (UnitCube n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (w : Fin N → (Fin n → ℝ)) (b : Fin N → ℝ) (α : Fin N → ℝ),
      ∀ x ∈ UnitCube n,
        |f x - neuralNetFun σ N w b α x| < ε := by
  have h_dense : Dense (neuralNetRange (n := n) σ hσ_cont) := neuralNet_dense hJD σ hσ_cont hσ_sig
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

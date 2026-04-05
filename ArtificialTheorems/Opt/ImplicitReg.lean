/-
Implicit Regularization of Gradient Descent — Proof

Proves that gradient descent on overparameterized linear regression with w(0) = 0
converges to the minimum ℓ₂-norm interpolant w̄ = Xᵀ(XXᵀ)⁻¹y.

Approach (Option B — discrete GD):
1. Subspace invariance: w_k ∈ row(X) for all k (by induction)
2. Reparameterize: w_k = Xᵀ α_k, derive α dynamics
3. Convergence: α_k → (XXᵀ)⁻¹y via contraction on the residual
4. Minimum norm: any w in row(X) with Xw = y has minimum norm

References:
- Zhang et al. 2017, "Understanding Deep Learning Requires Rethinking Generalization"
- Hegde lecture notes, Chapter 7
-/

import Mathlib

open Matrix Filter Topology BigOperators
open scoped RealInnerProductSpace Matrix.Norms.Elementwise Matrix.Norms.L2Operator

noncomputable section

namespace ImplicitReg

variable {n d : ℕ}

/-- The gradient descent iteration for linear regression:
    w_{k+1} = w_k - η · Xᵀ(Xw_k - y) -/
def gdIter (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    : (Fin d → ℝ) → (Fin d → ℝ) :=
  fun w => w - η • Xᵀ.mulVec (X.mulVec w - y)

/-- The GD sequence starting from w₀ = 0. -/
def gdSeq (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    : ℕ → (Fin d → ℝ)
  | 0 => 0
  | k + 1 => gdIter X y η (gdSeq X y η k)

/-- The minimum-norm interpolant: w̄ = Xᵀ(XXᵀ)⁻¹y -/
def minNormSol (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) : Fin d → ℝ :=
  Xᵀ.mulVec ((X * Xᵀ)⁻¹.mulVec y)

/-! ### Part 1: Subspace Invariance -/

/-- The GD update preserves membership in row(X).
    If w = Xᵀ α, then gdIter X y η w = Xᵀ α' for some α'. -/
lemma gdIter_in_row_space (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (w : Fin d → ℝ) (α : Fin n → ℝ) (hw : w = Xᵀ.mulVec α) :
    ∃ α' : Fin n → ℝ, gdIter X y η w = Xᵀ.mulVec α' := by
  -- gdIter X y η w = w - η • Xᵀ(Xw - y)
  --               = Xᵀα - η • Xᵀ(XXᵀα - y)
  --               = Xᵀ(α - η • (XXᵀα - y))
  use α - η • (X.mulVec (Xᵀ.mulVec α) - y)
  -- gdIter X y η (Xᵀ α) = (Xᵀ α) - η • Xᵀ(X(Xᵀ α) - y) = Xᵀ(α - η(XXᵀ α - y))
  simp only [gdIter, hw, mulVec_sub, mulVec_smul, smul_sub]

/-- Subspace invariance: GD iterates stay in row(X). -/
theorem gd_in_row_space (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ) (k : ℕ) :
    ∃ α : Fin n → ℝ, gdSeq X y η k = Xᵀ.mulVec α := by
  induction k with
  | zero =>
    use 0
    simp [gdSeq]
  | succ k ih =>
    obtain ⟨α, hα⟩ := ih
    exact gdIter_in_row_space X y η _ α hα

/-! ### Part 2: Reparameterized Dynamics

When w_k = Xᵀ α_k, the GD iteration becomes:
  α_{k+1} = α_k - η(XXᵀ α_k - y)
           = (I - η·XXᵀ) α_k + η·y

This is a linear iteration α_{k+1} = A α_k + b where:
  A = I - η·XXᵀ,  b = η·y
-/

/-- The reparameterized iteration matrix. -/
def iterMatrix (X : Matrix (Fin n) (Fin d) ℝ) (η : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - η • (X * Xᵀ)

/-- The α-space dynamics: if w_k = Xᵀ α_k and w_{k+1} = gdIter X y η w_k,
    then α_{k+1} = (I - η XXᵀ) α_k + η y. -/
lemma alpha_dynamics (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (α : Fin n → ℝ) :
    gdIter X y η (Xᵀ.mulVec α)
      = Xᵀ.mulVec ((iterMatrix X η).mulVec α + η • y) := by
  simp only [gdIter, iterMatrix]
  -- Rewrite using mulVec linearity
  -- LHS: Xᵀ *ᵥ α - η • (Xᵀ *ᵥ (X *ᵥ (Xᵀ *ᵥ α) - y))
  -- RHS: Xᵀ *ᵥ ((1 - η • (X * Xᵀ)) *ᵥ α + η • y)
  simp only [mulVec_add, mulVec_smul, sub_mulVec, one_mulVec, smul_mulVec,
    mulVec_mulVec, mulVec_sub]
  -- Now both sides should reduce to the same thing
  module

/-- The α-sequence satisfying w_k = Xᵀ α_k. -/
def alphaSeq (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ) : ℕ → Fin n → ℝ
  | 0 => 0
  | k + 1 => (iterMatrix X η).mulVec (alphaSeq X y η k) + η • y

/-- The affine self-map on α-space underlying the reparameterized GD dynamics. -/
def alphaStep (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  fun α => (iterMatrix X η).mulVec α + η • y

/-- The same α-update, but on the genuine Euclidean/L2 space. This is the ambient space
    in which the spectral bound for `I - η XXᵀ` is expected to apply. -/
def alphaStepEuclidean (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun α => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (iterMatrix X η) α + WithLp.toLp 2 (η • y)

@[simp] lemma alphaStepEuclidean_toLp (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (α : Fin n → ℝ) :
    alphaStepEuclidean X y η (WithLp.toLp 2 α) = WithLp.toLp 2 (alphaStep X y η α) := by
  simp [alphaStepEuclidean, alphaStep]

@[simp] lemma ofLp_alphaStepEuclidean (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (α : EuclideanSpace ℝ (Fin n)) :
    WithLp.ofLp (alphaStepEuclidean X y η α) = alphaStep X y η (WithLp.ofLp α) := by
  simp [alphaStepEuclidean, alphaStep]

lemma alphaSeq_eq_iterate_alphaStep (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (k : ℕ) : alphaSeq X y η k = (alphaStep X y η)^[k] 0 := by
  induction k with
  | zero => simp [alphaSeq]
  | succ k ih => simp [alphaSeq, alphaStep, ih, Function.iterate_succ_apply']

/-- Iterates of `alphaStepEuclidean` correspond to `WithLp.toLp 2` applied to iterates
    of `alphaStep`. This is the bridge between the coordinate-level recurrence and the
    Euclidean-space contraction argument. -/
lemma alphaStepEuclidean_iterate (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (k : ℕ) :
    (alphaStepEuclidean X y η)^[k] 0 = WithLp.toLp 2 ((alphaStep X y η)^[k] 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, alphaStepEuclidean_toLp]

/-- The w-sequence equals Xᵀ times the α-sequence. -/
lemma gdSeq_eq_transpose_alphaSeq (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (k : ℕ) : gdSeq X y η k = Xᵀ.mulVec (alphaSeq X y η k) := by
  induction k with
  | zero => simp [gdSeq, alphaSeq]
  | succ k ih =>
    simp only [gdSeq, alphaSeq]
    rw [ih, alpha_dynamics]

/-! ### Part 3: Convergence of the α-iteration

The iteration α_{k+1} = A α_k + η y has fixed point α* = (I - A)⁻¹(η y) = (XXᵀ)⁻¹ y
(when XXᵀ is invertible).

The residual r_k = α_k - α* satisfies r_{k+1} = A r_k, so ‖r_k‖ ≤ ‖A‖^k ‖r_0‖.
When ‖A‖ = ‖I - η XXᵀ‖ < 1 (ensured by the step size condition), this converges to 0.
-/

/-- The fixed point of the α-iteration is (XXᵀ)⁻¹ y. -/
def alphaLimit (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  (X * Xᵀ)⁻¹.mulVec y

/-- XXᵀ is invertible when X has full row rank. -/
lemma xxT_invertible (X : Matrix (Fin n) (Fin d) ℝ) (hX : X.rank = n) :
    IsUnit (X * Xᵀ).det := by
  -- Step 1: rank(XXᵀ) = rank(X) = n
  have hrank : (X * Xᵀ).rank = n := by
    have : Xᴴ = Xᵀ := by ext i j; simp [conjTranspose, transpose, star]
    rw [← this, rank_self_mul_conjTranspose, hX]
  -- Step 2: rank = n for n×n matrix → IsUnit det
  unfold Matrix.rank at hrank
  have hfin : Module.finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  have htop : (X * Xᵀ).mulVecLin.range = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hrank, hfin])
  have hsurj := LinearMap.range_eq_top.mp htop
  have hinj := Module.End.injective_of_surjective_fin hsurj
  exact (isUnit_iff_isUnit_det _).mp (mulVec_injective_iff_isUnit.mp hinj)

/-- The residual r_k = α_k - α* satisfies r_{k+1} = A r_k. -/
-- Helper: alphaLimit is a fixed point of the iteration
lemma alphaLimit_fixed_point (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (hX : X.rank = n) :
    alphaStep X y η (alphaLimit X y) = alphaLimit X y := by
  simp only [alphaStep, iterMatrix, alphaLimit]
  rw [sub_mulVec, one_mulVec, Matrix.smul_mulVec, mulVec_mulVec,
    mul_nonsing_inv _ (xxT_invertible X hX), one_mulVec]
  simp [sub_add_cancel]

lemma alphaLimit_fixed_point_euclidean (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (hX : X.rank = n) :
    alphaStepEuclidean X y η (WithLp.toLp 2 (alphaLimit X y)) =
      WithLp.toLp 2 (alphaLimit X y) := by
  simpa using congrArg (WithLp.toLp 2) (alphaLimit_fixed_point X y η hX)

lemma residual_dynamics (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (hX : X.rank = n) (k : ℕ) :
    alphaSeq X y η (k + 1) - alphaLimit X y
    = (iterMatrix X η).mulVec (alphaSeq X y η k - alphaLimit X y) := by
  rw [mulVec_sub]
  ext i
  have hfix := congr_fun (alphaLimit_fixed_point X y η hX) i
  have hfix' : (iterMatrix X η).mulVec (alphaLimit X y) i + η * y i = alphaLimit X y i := by
    simpa [alphaStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hfix
  simp [alphaSeq, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- The linear part of the α-update is a strict contraction in the Euclidean/L2 operator norm.

    The continuous linear map `Matrix.toEuclideanCLM (iterMatrix X η)` on
    `EuclideanSpace ℝ (Fin n)` has operator norm strictly less than 1.
    This is the correct formulation: the spectral argument for the symmetric matrix
    `I - η XXᵀ` bounds the L2 operator norm, matching the Euclidean inner product.

    The mathematical argument:
    • `X * Xᵀ` is symmetric positive semidefinite, with eigenvalues in `[0, ‖X * Xᵀ‖_op]`.
    • `X.rank = n` forces all `n` eigenvalues to be strictly positive.
    • `iterMatrix X η = I - η (X * Xᵀ)` has eigenvalues `1 - η σᵢ`.
    • The step-size condition `η * ‖X * Xᵀ‖_op < 2` ensures each `|1 - η σᵢ| < 1`.
    • Therefore the L2 operator norm (= spectral radius for Hermitian matrices) is `< 1`.

    The proof uses the spectral theorem for the Hermitian matrix `X * Xᵀ`,
    decomposes `I - η(XXᵀ)` in the eigenbasis, applies unitary invariance of
    the L2 operator norm, and bounds each `|1 - η σᵢ| < 1`. -/
private lemma xxT_isHermitian (X : Matrix (Fin n) (Fin d) ℝ) :
    (X * Xᵀ).IsHermitian := by
  rw [show Xᵀ = Xᴴ from (conjTranspose_eq_transpose_of_trivial X).symm]
  exact isHermitian_mul_conjTranspose_self X

lemma iterMatrix_euclidean_opNorm_lt_one (X : Matrix (Fin n) (Fin d) ℝ) (η : ℝ)
    (hX : X.rank = n) (hη_pos : 0 < η)
    (hη_small : η * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (X * Xᵀ)‖ < 2) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (iterMatrix X η)‖ < 1 := by
  classical
  rw [l2_opNorm_toEuclideanCLM]
  rw [l2_opNorm_toEuclideanCLM] at hη_small
  have hB := xxT_isHermitian X
  set σ := hB.eigenvalues
  set U := hB.eigenvectorUnitary
  -- Spectral theorem: XXᵀ = U * diagonal(σ) * U*
  have hB_spec : X * Xᵀ =
      (Unitary.conjStarAlgAut ℝ _ U) (diagonal ((RCLike.ofReal (K := ℝ)) ∘ σ)) :=
    hB.spectral_theorem (𝕜 := ℝ)
  -- Express iterMatrix = U * (I - η diag(σ)) * U*
  have key : iterMatrix X η =
      (Unitary.conjStarAlgAut ℝ _ U) (1 - η • diagonal ((RCLike.ofReal (K := ℝ)) ∘ σ)) := by
    unfold iterMatrix
    rw [hB_spec, map_sub, map_one, map_smul]
  -- Reduce to ‖diagonal(1 - η σ)‖ < 1 via unitary invariance
  rw [key, Unitary.conjStarAlgAut_apply]
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.prop)]
  rw [CStarRing.norm_coe_unitary_mul]
  simp only [RCLike.ofReal_real_eq_id, Function.id_comp]
  rw [show (1 : Matrix (Fin n) (Fin n) ℝ) - η • diagonal σ = diagonal (1 - η • σ) by
    ext i j; simp only [sub_apply, one_apply, smul_apply, diagonal_apply, smul_eq_mul]
    split <;> simp]
  rw [l2_opNorm_diagonal]
  -- Eigenvalues of XXᵀ are nonneg (PSD)
  have hσ_nonneg : ∀ i, 0 ≤ σ i := by
    intro i
    have : (X * Xᵀ).PosSemidef := by
      rw [show Xᵀ = Xᴴ from (conjTranspose_eq_transpose_of_trivial X).symm]
      exact posSemidef_self_mul_conjTranspose X
    exact this.eigenvalues_nonneg i
  -- ‖XXᵀ‖ = sup|σ_i| via spectral decomposition
  have hXXt_norm : ‖X * Xᵀ‖ = ‖σ‖ := by
    conv_lhs => rw [hB_spec, Unitary.conjStarAlgAut_apply]
    rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.prop)]
    rw [CStarRing.norm_coe_unitary_mul]
    simp only [RCLike.ofReal_real_eq_id, Function.id_comp]
    rw [l2_opNorm_diagonal]
  -- Each eigenvalue is bounded by the norm
  have hσ_le_norm : ∀ i, σ i ≤ ‖X * Xᵀ‖ := by
    intro i; rw [hXXt_norm]
    exact le_trans (le_abs_self _) (norm_le_pi_norm σ i)
  -- η * σ_i < 2 from the step-size hypothesis
  have hησ_lt_2 : ∀ i, η * σ i < 2 := by
    intro i
    calc η * σ i ≤ η * ‖X * Xᵀ‖ :=
          mul_le_mul_of_nonneg_left (hσ_le_norm i) hη_pos.le
      _ < 2 := hη_small
  -- All eigenvalues are strictly positive (rank = n forces no zero eigenvalues)
  have hσ_pos : ∀ i, 0 < σ i := by
    have h_rank : (X * Xᵀ).rank = Fintype.card {i // σ i ≠ 0} :=
      hB.rank_eq_card_non_zero_eigs
    have h_xxT_rank : (X * Xᵀ).rank = n := by
      rw [show Xᵀ = Xᴴ from (conjTranspose_eq_transpose_of_trivial X).symm]
      rw [Matrix.rank_self_mul_conjTranspose X]; exact hX
    rw [h_xxT_rank] at h_rank
    have h_all_nonzero : ∀ i, σ i ≠ 0 := by
      by_contra h_neg; push_neg at h_neg; obtain ⟨i, hi⟩ := h_neg
      have h1 : Fintype.card {j : Fin n // σ j ≠ 0} < Fintype.card (Fin n) :=
        Fintype.card_subtype_lt (by rwa [not_not])
      rw [Fintype.card_fin] at h1; linarith
    intro i; exact lt_of_le_of_ne (hσ_nonneg i) (Ne.symm (h_all_nonzero i))
  -- Conclude: sup_i |1 - η σ_i| < 1, since 0 < η σ_i < 2
  rw [pi_norm_lt_iff one_pos]
  intro i
  simp only [Pi.sub_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
  rw [Real.norm_eq_abs, abs_lt]
  exact ⟨by linarith [hησ_lt_2 i], by linarith [mul_pos hη_pos (hσ_pos i)]⟩

/-- The α-sequence converges to (XXᵀ)⁻¹ y.

    The proof works in `EuclideanSpace ℝ (Fin n)` where the spectral bound on
    `I - η XXᵀ` gives a genuine L2 contraction, then transports convergence back
    to `Fin n → ℝ` via the continuous equivalence `EuclideanSpace.equiv`. -/
theorem alphaSeq_tendsto (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (hX : X.rank = n)
    (hA_contr : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (iterMatrix X η)‖ < 1) :
    Tendsto (alphaSeq X y η) atTop (nhds (alphaLimit X y)) := by
  -- Work in EuclideanSpace ℝ (Fin n) where the L2 contraction applies
  let AE : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (iterMatrix X η)
  have hκ_lt : (⟨‖AE‖, norm_nonneg _⟩ : NNReal) < 1 := hA_contr
  have hAE_lip : LipschitzWith (⟨‖AE‖, norm_nonneg _⟩ : NNReal) AE :=
    AE.lipschitzWith_of_opNorm_le (le_refl _)
  -- alphaStepEuclidean is contracting with the same constant
  have hstep_lip : LipschitzWith (⟨‖AE‖, norm_nonneg _⟩ : NNReal) (alphaStepEuclidean X y η) := by
    refine LipschitzWith.of_dist_le_mul fun α β => ?_
    simp only [dist_eq_norm, NNReal.coe_mk]
    show ‖alphaStepEuclidean X y η α - alphaStepEuclidean X y η β‖ ≤ ‖AE‖ * ‖α - β‖
    have h : alphaStepEuclidean X y η α - alphaStepEuclidean X y η β = AE (α - β) := by
      show (AE α + _) - (AE β + _) = AE (α - β)
      rw [add_sub_add_right_eq_sub, ← map_sub]
    rw [h]; exact AE.le_opNorm _
  have hstep_contr : ContractingWith (⟨‖AE‖, norm_nonneg _⟩ : NNReal) (alphaStepEuclidean X y η) :=
    ⟨hκ_lt, hstep_lip⟩
  -- Identify the Banach fixed point with alphaLimit
  have hfix : Function.IsFixedPt (alphaStepEuclidean X y η) (WithLp.toLp 2 (alphaLimit X y)) :=
    alphaLimit_fixed_point_euclidean X y η hX
  have hfixed : WithLp.toLp 2 (alphaLimit X y) = hstep_contr.fixedPoint :=
    hstep_contr.fixedPoint_unique hfix
  -- Convergence in EuclideanSpace
  have hiter : (fun k => (alphaStepEuclidean X y η)^[k] 0) =
      fun k => WithLp.toLp 2 (alphaSeq X y η k) := by
    funext k; rw [alphaStepEuclidean_iterate, alphaSeq_eq_iterate_alphaStep]
  have hconv_E : Tendsto (fun k => WithLp.toLp 2 (alphaSeq X y η k)) atTop
      (nhds (WithLp.toLp 2 (alphaLimit X y))) := by
    rw [hfixed, ← hiter]; exact hstep_contr.tendsto_iterate_fixedPoint 0
  -- Transport back to Fin n → ℝ via the continuous equivalence
  exact (EuclideanSpace.equiv (Fin n) ℝ).continuous.continuousAt.tendsto.comp hconv_E

/-- The GD sequence converges to the minimum-norm solution. -/
theorem gdSeq_tendsto (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (_hnd : n < d) (hX : X.rank = n)
    (hA_contr : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (iterMatrix X η)‖ < 1) :
    Tendsto (gdSeq X y η) atTop (nhds (minNormSol X y)) := by
  have hconv := alphaSeq_tendsto X y η hX hA_contr
  have heq : gdSeq X y η = Xᵀ.mulVec ∘ alphaSeq X y η := by
    funext k; exact gdSeq_eq_transpose_alphaSeq X y η k
  rw [heq, show minNormSol X y = Xᵀ.mulVec (alphaLimit X y) from rfl]
  have hcont : Continuous (Xᵀ.mulVecLin : (Fin n → ℝ) →ₗ[ℝ] (Fin d → ℝ)) :=
    LinearMap.continuous_of_finiteDimensional _
  exact hcont.continuousAt.tendsto.comp hconv

/-! ### Part 4: Interpolation Property -/

/-- The minimum-norm solution interpolates: X w̄ = y.
    Proof: X (Xᵀ (XXᵀ)⁻¹ y) = (XXᵀ)(XXᵀ)⁻¹ y = y. -/
theorem minNormSol_interpolates (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hX : X.rank = n) :
    X.mulVec (minNormSol X y) = y := by
  simp only [minNormSol]
  rw [mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ (xxT_invertible X hX), one_mulVec]

/-! ### Part 5: Minimum Norm Property

Key idea: Decompose any interpolant v = w̄ + z where z ∈ ker(X).
Since w̄ ∈ row(X) and z ∈ ker(X), and row(X) ⊥ ker(X), we get
‖v‖² = ‖w̄‖² + ‖z‖², so ‖v‖ ≥ ‖w̄‖.
-/

/-- The minimum-norm solution lies in the row space of X. -/
lemma minNormSol_in_row_space (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) :
    ∃ α : Fin n → ℝ, minNormSol X y = Xᵀ.mulVec α := by
  exact ⟨(X * Xᵀ)⁻¹.mulVec y, rfl⟩

/-- Row space and null space are orthogonal:
    If w = Xᵀ α and X z = 0, then the dot product ∑ i, (Xᵀ α)_i * z_i = 0. -/
lemma row_space_perp_null_space (X : Matrix (Fin n) (Fin d) ℝ)
    (α : Fin n → ℝ) (z : Fin d → ℝ) (hz : X.mulVec z = 0) :
    dotProduct (Xᵀ.mulVec α) z = 0 := by
  -- (Xᵀ α) ⬝ᵥ z = (α ᵥ* X) ⬝ᵥ z = α ⬝ᵥ (X z) = α ⬝ᵥ 0 = 0
  rw [mulVec_transpose]
  rw [← dotProduct_mulVec]
  rw [hz, dotProduct_zero]

/-- Correct ℓ₂-style minimality statement in coordinate form:
    among all interpolants, `minNormSol X y` minimizes the squared Euclidean norm,
    expressed as `dotProduct w w`.

    This is the narrowest viable repair of the false sup-norm statement above: we keep
    the ambient coordinate type `Fin d → ℝ`, but measure size using the inner-product
    quadratic form instead of the inherited `‖·‖` on functions. -/
theorem minNormSol_min_dotProduct' (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hX : X.rank = n)
    (v : Fin d → ℝ) (hv : X.mulVec v = y) :
    dotProduct (minNormSol X y) (minNormSol X y) ≤ dotProduct v v := by
  let wbar : Fin d → ℝ := minNormSol X y
  let z : Fin d → ℝ := v - wbar
  have hwbar_interp : X.mulVec wbar = y := minNormSol_interpolates X y hX
  have hz_null : X.mulVec z = 0 := by
    dsimp [z]
    rw [mulVec_sub, hv, hwbar_interp, sub_self]
  obtain ⟨α, hwbar_row : wbar = Xᵀ.mulVec α⟩ := minNormSol_in_row_space X y
  have hperp : dotProduct wbar z = 0 := by
    rw [hwbar_row]
    exact row_space_perp_null_space X α z hz_null
  have hz_nonneg : 0 ≤ dotProduct z z := by
    simpa [dotProduct] using Finset.sum_nonneg (fun i _ => by
      have hi : 0 ≤ z i * z i := by nlinarith [sq_nonneg (z i)]
      exact hi)
  have hv_decomp : v = wbar + z := by
    dsimp [z]
    abel
  calc
    dotProduct wbar wbar ≤ dotProduct wbar wbar + dotProduct z z := by linarith
    _ = dotProduct (wbar + z) (wbar + z) := by
      have hzperp : dotProduct z wbar = 0 := by rw [dotProduct_comm, hperp]
      have hs1 : ∑ x, wbar x * z x = 0 := by simpa [dotProduct] using hperp
      have hs2 : ∑ x, z x * wbar x = 0 := by simpa [dotProduct] using hzperp
      simp [dotProduct, Finset.sum_add_distrib, add_mul, mul_add, hs1, hs2]
    _ = dotProduct v v := by rw [hv_decomp]

/-- Public repaired minimality theorem: among all interpolants, `minNormSol X y`
    minimizes the squared Euclidean norm in coordinate form.

    This replaces the earlier false `‖·‖`-based statement on `Fin d → ℝ`, where the
    inherited norm is the sup norm rather than the ℓ₂ norm. We keep the same ambient
    coordinates and expose the correct quadratic-form statement instead. -/
theorem minNormSol_min_norm (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hX : X.rank = n) (_hnd : n < d)
    (v : Fin d → ℝ) (hv : X.mulVec v = y) :
    dotProduct (minNormSol X y) (minNormSol X y) ≤ dotProduct v v := by
  exact minNormSol_min_dotProduct' X y hX v hv

/-! ### Main Theorem Assembly -/

/-- Internal assembly: Gradient descent on overparameterized linear regression
    converges to the minimum ℓ₂-bias solution, given the Euclidean/L2 operator norm
    contraction hypothesis directly.

    Use `implicit_l2_bias` for the public-facing version with step-size hypotheses. -/
theorem implicit_l2_bias_of_contraction (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hnd : n < d) (hX : X.rank = n) (η : ℝ)
    (hA_contr : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (iterMatrix X η)‖ < 1) :
    Tendsto (gdSeq X y η) atTop (nhds (minNormSol X y))
    ∧ X.mulVec (minNormSol X y) = y
    ∧ ∀ v : Fin d → ℝ, X.mulVec v = y →
        dotProduct (minNormSol X y) (minNormSol X y) ≤ dotProduct v v :=
  ⟨gdSeq_tendsto X y η hnd hX hA_contr,
   minNormSol_interpolates X y hX,
   fun v hv => minNormSol_min_norm X y hX hnd v hv⟩

/-- **Main theorem (literature-facing)**: Gradient descent on overparameterized linear
    regression with `w₀ = 0` converges to the minimum ℓ₂-norm interpolant
    `w̄ = Xᵀ(XXᵀ)⁻¹y`.

    Hypotheses:
    - `X` has full row rank (`X.rank = n`)
    - The system is overparameterized (`n < d`)
    - Step size `η` satisfies `0 < η` and `η · ‖XXᵀ‖_L2 < 2`

    Conclusions:
    1. The GD iterates converge to `w̄`
    2. `w̄` interpolates: `X w̄ = y`
    3. `w̄` minimizes the squared ℓ₂ norm (as `dotProduct`) among all interpolants

    The step-size condition is expressed via the L2 operator norm
    `‖Matrix.toEuclideanCLM (X * Xᵀ)‖`, which equals the largest eigenvalue of `XXᵀ`
    (equivalently the largest singular value of `X` squared). -/
theorem implicit_l2_bias (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hnd : n < d) (hX : X.rank = n) (η : ℝ)
    (hη_pos : 0 < η)
    (hη_small : η * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (X * Xᵀ)‖ < 2) :
    Tendsto (gdSeq X y η) atTop (nhds (minNormSol X y))
    ∧ X.mulVec (minNormSol X y) = y
    ∧ ∀ v : Fin d → ℝ, X.mulVec v = y →
        dotProduct (minNormSol X y) (minNormSol X y) ≤ dotProduct v v :=
  implicit_l2_bias_of_contraction X y hnd hX η
    (iterMatrix_euclidean_opNorm_lt_one X η hX hη_pos hη_small)

end ImplicitReg

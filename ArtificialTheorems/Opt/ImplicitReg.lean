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
import ArtificialTheoremsSpec.Opt.ImplicitRegSpec

open Matrix Filter Topology BigOperators
open scoped RealInnerProductSpace Matrix.Norms.Elementwise

noncomputable section

namespace ImplicitReg

variable {n d : ℕ}

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
theorem gd_in_row_space' (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ) (k : ℕ) :
    ∃ α : Fin n → ℝ, gdSeq X y η k = Xᵀ.mulVec α := by
  induction k with
  | zero =>
    use 0
    simp [gdSeq, dotProduct]
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
  -- Xᵀα - η • Xᵀ(XXᵀα - y) = Xᵀ((I - η XXᵀ)α + ηy)
  sorry

/-- The α-sequence satisfying w_k = Xᵀ α_k. -/
def alphaSeq (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ) : ℕ → Fin n → ℝ
  | 0 => 0
  | k + 1 => (iterMatrix X η).mulVec (alphaSeq X y η k) + η • y

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
  sorry

/-- The residual r_k = α_k - α* satisfies r_{k+1} = A r_k. -/
lemma residual_dynamics (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (hX : X.rank = n) (k : ℕ) :
    alphaSeq X y η (k + 1) - alphaLimit X y
    = (iterMatrix X η).mulVec (alphaSeq X y η k - alphaLimit X y) := by
  sorry

/-- The operator norm of I - η XXᵀ is less than 1 for appropriate η. -/
lemma iterMatrix_norm_lt_one (X : Matrix (Fin n) (Fin d) ℝ) (η : ℝ)
    (hη_pos : 0 < η) (hη_small : η < 2 / ‖Xᵀ * X‖) :
    ‖iterMatrix X η‖ < 1 := by
  sorry

/-- The α-sequence converges to (XXᵀ)⁻¹ y. -/
theorem alphaSeq_tendsto (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (hX : X.rank = n) (hη_pos : 0 < η) (hη_small : η < 2 / ‖Xᵀ * X‖) :
    Tendsto (alphaSeq X y η) atTop (nhds (alphaLimit X y)) := by
  sorry

/-- The GD sequence converges to the minimum-norm solution. -/
theorem gdSeq_tendsto (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ)
    (hnd : n < d) (hX : X.rank = n)
    (hη_pos : 0 < η) (hη_small : η < 2 / ‖Xᵀ * X‖) :
    Tendsto (gdSeq X y η) atTop (nhds (minNormSol X y)) := by
  -- gdSeq = Xᵀ ∘ alphaSeq, and Xᵀ.mulVec is continuous
  -- alphaSeq → alphaLimit = (XXᵀ)⁻¹ y
  -- so gdSeq → Xᵀ (XXᵀ)⁻¹ y = minNormSol
  sorry

/-! ### Part 4: Interpolation Property -/

/-- The minimum-norm solution interpolates: X w̄ = y.
    Proof: X (Xᵀ (XXᵀ)⁻¹ y) = (XXᵀ)(XXᵀ)⁻¹ y = y. -/
theorem minNormSol_interpolates' (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hX : X.rank = n) :
    X.mulVec (minNormSol X y) = y := by
  -- minNormSol X y = Xᵀ.mulVec ((XXᵀ)⁻¹.mulVec y)
  -- X.mulVec (Xᵀ.mulVec ((XXᵀ)⁻¹.mulVec y))
  --   = (X * Xᵀ).mulVec ((XXᵀ)⁻¹.mulVec y)    [by mulVec_mulVec]
  --   = ((XXᵀ) * (XXᵀ)⁻¹).mulVec y             [by mulVec_mulVec]
  --   = 1.mulVec y                                [by mul_nonsing_inv]
  --   = y                                         [by one_mulVec]
  sorry

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

/-- The minimum-norm solution has smallest norm among all interpolants. -/
theorem minNormSol_min_norm' (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hX : X.rank = n) (hnd : n < d)
    (v : Fin d → ℝ) (hv : X.mulVec v = y) :
    ‖minNormSol X y‖ ≤ ‖v‖ := by
  -- Decompose v = w̄ + z where z = v - w̄
  -- Then X z = X v - X w̄ = y - y = 0, so z ∈ ker(X)
  -- w̄ ∈ row(X), so ⟨w̄, z⟩ = 0
  -- ‖v‖² = ‖w̄ + z‖² = ‖w̄‖² + 2⟨w̄,z⟩ + ‖z‖² = ‖w̄‖² + ‖z‖² ≥ ‖w̄‖²
  sorry

/-! ### Main Theorem Assembly -/

/-- Main theorem: Gradient descent on overparameterized linear regression
    converges to the minimum ℓ₂-norm interpolant. -/
theorem implicit_l2_bias' (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hnd : n < d) (hX : X.rank = n)
    (η : ℝ) (hη_pos : 0 < η) (hη_small : η < 2 / ‖Xᵀ * X‖) :
    Tendsto (gdSeq X y η) atTop (nhds (minNormSol X y))
    ∧ X.mulVec (minNormSol X y) = y
    ∧ ∀ v : Fin d → ℝ, X.mulVec v = y → ‖minNormSol X y‖ ≤ ‖v‖ :=
  ⟨gdSeq_tendsto X y η hnd hX hη_pos hη_small,
   minNormSol_interpolates' X y hX,
   fun v hv => minNormSol_min_norm' X y hX hnd v hv⟩

end ImplicitReg

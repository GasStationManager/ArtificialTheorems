/-
Implicit Regularization of Gradient Descent — Specification

Gradient descent on overparameterized linear regression (n < d, full row rank X)
with w(0) = 0 converges to the minimum ℓ₂-norm interpolant w̄ = Xᵀ(XXᵀ)⁻¹y.

This is the discrete-time version (Option B from the scoping document).
-/

import Mathlib

open Matrix Filter Topology BigOperators
open scoped RealInnerProductSpace Matrix.Norms.Elementwise

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

/-- Main theorem: GD on overparameterized linear regression converges to the
    minimum ℓ₂-norm interpolant.

    Hypotheses:
    - X has full row rank (rank n)
    - The system is overparameterized (n < d)
    - Step size η is in (0, 2/‖XᵀX‖)

    Conclusions:
    1. The GD iterates converge to w̄ = Xᵀ(XXᵀ)⁻¹y
    2. w̄ interpolates the data: Xw̄ = y
    3. w̄ has minimum ℓ₂-norm among all interpolants -/
theorem implicit_l2_bias
    (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hnd : n < d)
    (hX : X.rank = n)
    (η : ℝ) (hη_pos : 0 < η) (hη_small : η < 2 / ‖Xᵀ * X‖) :
    -- (1) Convergence of GD iterates
    Tendsto (gdSeq X y η) atTop (nhds (minNormSol X y))
    -- (2) The limit interpolates: Xw̄ = y
    ∧ X.mulVec (minNormSol X y) = y
    -- (3) Minimum norm: for any interpolant v, ‖w̄‖ ≤ ‖v‖
    ∧ ∀ v : Fin d → ℝ, X.mulVec v = y →
        ‖minNormSol X y‖ ≤ ‖v‖ := by
  sorry

/-- Subspace invariance: GD iterates stay in row(X) when starting from 0.
    Formally: w_k = Xᵀ α_k for some α_k. -/
theorem gd_in_row_space
    (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (η : ℝ) (k : ℕ) :
    ∃ α : Fin n → ℝ, gdSeq X y η k = Xᵀ.mulVec α := by
  sorry

/-- The minimum-norm solution interpolates the data when X has full row rank. -/
theorem minNormSol_interpolates
    (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hX : X.rank = n) :
    X.mulVec (minNormSol X y) = y := by
  sorry

/-- The minimum-norm solution has smallest ℓ₂-norm among all interpolants. -/
theorem minNormSol_min_norm
    (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hX : X.rank = n) (hnd : n < d)
    (v : Fin d → ℝ) (hv : X.mulVec v = y) :
    ‖minNormSol X y‖ ≤ ‖v‖ := by
  sorry

end ImplicitReg

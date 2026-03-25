# Implicit Regularization — Formalization Scoping Document

## Overview

We scope the formalization of **implicit regularization results** for gradient flow on overparameterized models. These results show that gradient descent/flow biases toward "simple" solutions (minimum norm, sparse, low-rank) without explicit regularization — the algorithmic analog of Occam's Razor.

**Connection to the verifiability thesis:** These theorems demonstrate that SGD creates *mathematically characterizable structure* in learned models. If gradient flow provably converges to minimum-norm solutions, then:
- The learned weights have **compact mathematical descriptions** (they solve specific optimization problems)
- These descriptions are **formally verifiable** (we can state and prove the characterization in Lean)
- The same structural simplicity that enables generalization also enables formal reasoning about the network

This is "verifiability and generalization as two faces of the same coin" made precise: the implicit bias that helps generalization also creates structure amenable to formal proof.

---

## Target 1: GF on Linear Regression → Minimum ℓ₂-Norm (Recommended First Target)

### Paper / Source
- Folklore result; clean proofs in Zhang et al. 2017 ("Understanding Deep Learning Requires Rethinking Generalization") and many textbooks
- Expositions: Hegde lecture notes (Ch. 7), Vershynin "High-Dimensional Probability"

### Setting
Overparameterized linear regression: n samples, d features, n < d (underdetermined).
- Data matrix X ∈ ℝ^{n×d} with rank n (full row rank)
- Labels y ∈ ℝ^n
- Loss: L(w) = ½‖y − Xw‖²
- Gradient flow: dw/dt = −∇L(w(t)) = Xᵀ(y − Xw(t)), with w(0) = 0

### Theorem Statement

**Theorem (Implicit ℓ₂-bias of gradient flow).**
Let X ∈ ℝ^{n×d} with n < d and rank(X) = n. Let y ∈ ℝ^n. Consider gradient flow on L(w) = ½‖y − Xw‖² with w(0) = 0. Then:

1. **Convergence:** w(t) converges as t → ∞ to some w̄ with Xw̄ = y (zero training loss).

2. **Minimum norm:** w̄ = Xᵀ(XXᵀ)⁻¹y, which is the unique solution to:
   ```
   min_w ‖w‖₂  subject to  Xw = y
   ```

### Proof Sketch

**Step 1: Subspace invariance.**
The gradient ∇L(w) = −Xᵀ(y − Xw) always lies in row(X) = span of rows of X. Since w(0) = 0 ∈ row(X), by the ODE dynamics, w(t) ∈ row(X) for all t ≥ 0.

*Formally:* w(t) = Xᵀα(t) for some α(t) ∈ ℝ^n. Substituting:
```
dα/dt = (y − XXᵀα(t))
```
This is a linear ODE in α with α(0) = 0.

**Step 2: Solve the linear ODE.**
Let K = XXᵀ ∈ ℝ^{n×n} (symmetric positive definite since rank(X) = n).
```
dα/dt = y − Kα(t)
```
Solution: α(t) = K⁻¹(I − e^{−Kt})y → K⁻¹y as t → ∞.

**Step 3: Recover w̄.**
w̄ = Xᵀα(∞) = Xᵀ(XXᵀ)⁻¹y = X⁺y (Moore-Penrose pseudoinverse).

**Step 4: Show this is minimum norm.**
Any solution to Xw = y can be written w = X⁺y + z where z ∈ ker(X).
Then ‖w‖² = ‖X⁺y‖² + ‖z‖² ≥ ‖X⁺y‖² = ‖w̄‖², with equality iff z = 0.

### Mathlib Dependencies

| Component | Mathlib Status | Notes |
|-----------|---------------|-------|
| Matrix multiplication, transpose | ✅ `Matrix.mul`, `Matrix.transpose` | Well-developed |
| Positive definite matrices | ✅ `Matrix.PosDef` | In `Mathlib.LinearAlgebra.Matrix.PosDef` |
| Matrix inverse | ✅ `Matrix.nonsing_inv` | For invertible matrices |
| Matrix exponential | ✅ `Matrix.exp` | In `Mathlib.Analysis.SpecialFunctions.Exponential` |
| Linear ODE solution | ⚠️ Partial | Picard-Lindelöf exists (`Mathlib.Analysis.ODE.PicardLindelof`), but explicit solution for linear systems needs work |
| Moore-Penrose pseudoinverse | ❌ Not in Mathlib | Would need to define X⁺ = Xᵀ(XXᵀ)⁻¹ and prove properties |
| Kernel / range orthogonal decomposition | ✅ `Submodule.IsCompl` | Orthogonal complement theory exists |
| Inner product / norm | ✅ `InnerProductSpace` | Well-developed |
| Convergence of matrix exponential | ⚠️ May need work | Need e^{−Kt} → 0 for K positive definite |

### Formalization Strategy

**Option A: ODE-based (faithful to the continuous-time proof)**
- Define gradient flow as the ODE
- Solve explicitly using matrix exponential
- Show convergence using spectral properties of K = XXᵀ
- *Estimated LOC:* 800–1200
- *Difficulty:* Medium-hard (ODE infrastructure is thin)

**Option B: Algebraic (avoid ODEs entirely)** ← **RECOMMENDED**
- State the theorem for *discrete* gradient descent: w_{k+1} = w_k − η·Xᵀ(Xw_k − y)
- Show w_k ∈ row(X) by induction
- Show convergence for η < 2/‖XXᵀ‖ using contraction argument
- Identify limit as X⁺y
- *Estimated LOC:* 400–700
- *Difficulty:* Medium (all linear algebra, no ODEs needed)

**Option C: Pure linear algebra (static characterization)**
- Skip the dynamics entirely
- Just prove: "The minimum ℓ₂-norm solution to Xw = y is w = Xᵀ(XXᵀ)⁻¹y"
- And: "If w(0) = 0 and w_k always stays in row(X), then any interpolating limit must be X⁺y"
- *Estimated LOC:* 200–400
- *Difficulty:* Easy-medium
- *Downside:* Less interesting — doesn't show the *dynamics* converge

### Estimated Difficulty & LOC

| Approach | LOC | Difficulty | Fidelity to "implicit reg" story |
|----------|-----|------------|----------------------------------|
| Option A (ODE) | 800–1200 | Hard | High |
| Option B (discrete GD) | 400–700 | Medium | High |
| Option C (static) | 200–400 | Easy | Low |

**Recommendation:** Option B. It captures the full story (dynamics + convergence + minimum norm) while staying within well-developed Mathlib territory (linear algebra + convergence of sequences).

---

## Target 2: GF on Diagonal Linear Networks → Minimum ℓ₁-Norm

### Paper
- Woodworth, Gunasekar, Lee, Moroshko, Savarse, Golan, Soudry, Srebro. "Kernel and Rich Regimes in Overparametrized Models." COLT 2020.
- Also: Li, Luo, Ma. "Implicit Bias of Gradient Descent on Reparameterized Models." 2021.

### Setting
Two-layer diagonal linear network with tied weights:
- Parameters: u ∈ ℝ^d
- Effective weights: w = u ∘ u (element-wise square)
- Prediction: ŷ = X(u ∘ u) for data matrix X ∈ ℝ^{n×d}
- Loss: L(u) = ½‖y − X(u ∘ u)‖²
- Gradient flow: du/dt = −∇_u L(u) = 2u ∘ Xᵀ(y − X(u ∘ u))
- Initialization: u(0) = α·𝟙 (uniform small initialization, α > 0)

### Theorem Statement

**Theorem (Implicit ℓ₁-bias of diagonal linear networks).**
Suppose gradient flow on L(u) converges to ū with X(ū ∘ ū) = y. Then w̄ = ū ∘ ū converges (as α → 0) to:
```
w* = arg min_w ‖w‖₁  subject to  Xw = y, w ≥ 0
```

### Proof Sketch (Woodworth et al. 2020)

**Step 1: Closed-form ODE solution.**
The gradient flow du_j/dt = 2u_j · [Xᵀe(t)]_j has solution:
```
u_j(t) = u_j(0) · exp(2[Xᵀ∫₀ᵗ e(s)ds]_j)
```
where e(t) = y − Xw(t) is the residual.

**Step 2: Effective weight dynamics.**
w_j(t) = u_j(t)² = α² · exp(4[Xᵀ∫₀ᵗ e(s)ds]_j)

**Step 3: KKT reverse-engineering.**
At convergence, w̄ = α² · exp(4Xᵀλ) where λ = ∫₀^∞ e(s)ds.
The implicit regularizer Q satisfies ∇Q(w̄) = Xᵀλ, giving:
```
∇_j Q(w) = log(w_j/α²)
```
Integrating: Q(w) = Σ_j [w_j log(w_j/α²) − w_j]

**Step 4: α → 0 limit.**
Q(w) = 2log(1/α)·Σ w_j + Σ(w_j log w_j − w_j)
As α → 0, the first term dominates → Q ≈ C_α · ‖w‖₁.

### Key Mathematical Dependencies

| Component | Mathlib Status | Notes |
|-----------|---------------|-------|
| Scalar ODE for each coordinate | ⚠️ Picard-Lindelöf exists | Need exponential solution |
| Exponential function properties | ✅ | Well-developed |
| KKT conditions for convex optimization | ❌ Not in Mathlib | Would need to build or sorry |
| ℓ₁ norm | ✅ `PiLp` or custom | Can define as Σ|w_j| |
| Constrained optimization characterization | ❌ | Major gap |
| Entropy/KL-divergence (the implicit regularizer) | ⚠️ Partial | `MeasureTheory.Measure.KLDiv` exists for measures, not vectors |

### Assessment

This is significantly harder than Target 1:
- The proof involves nonlinear ODEs (cubic gradient)
- KKT conditions for constrained optimization aren't in Mathlib
- The "reverse-engineering" argument is informal (assumes the bias is expressible as a regularizer)
- The α → 0 asymptotic argument needs careful handling

**Estimated LOC:** 1500–2500
**Difficulty:** Hard
**Recommendation:** Tackle only after Target 1 is complete, and possibly only the "static" characterization (that the KKT conditions of ℓ₁-minimization match the gradient flow limit).

---

## Target 3 (Future): Matrix Factorization → Nuclear Norm Minimization

### Paper
- Gunasekar, Woodworth, Bhojanapalli, Neyshabur, Srebro. "Implicit Regularization in Matrix Factorization." NeurIPS 2017. arXiv:1705.09280

### Status
This is actually a **conjecture** with partial theoretical evidence, not a fully proved theorem! The paper provides:
- Proof for the commutative case (when the initialization commutes with the data)
- Empirical evidence for the general case
- A proof under gradient flow (not gradient descent) with additional assumptions

The Arora et al. 2019 paper ("Implicit Regularization in Deep Matrix Factorization") provides further evidence but also does not fully resolve the conjecture.

**Not recommended for formalization** until the conjecture is resolved or we restrict to the proved special cases.

### What would be needed (for the commutative case)
- SVD / singular value decomposition: **NOT in Mathlib**
- Nuclear norm (sum of singular values): **NOT in Mathlib**
- Matrix factorization X = UVᵀ gradient flow analysis
- Spectral theory for non-symmetric matrices (for SVD)

This is a major undertaking (~3000+ LOC) primarily because SVD infrastructure doesn't exist in Mathlib.

---

## Comparison of Candidates

| Target | Setting | Math Depth | Mathlib Ready? | LOC Est. | Thesis Connection |
|--------|---------|-----------|----------------|----------|-------------------|
| **1: GF → min ℓ₂** | Linear regression | Linear algebra + sequences | ✅ Mostly | 400–700 | Shows simplest implicit bias |
| **2: DLN → min ℓ₁** | Diagonal linear net | ODEs + optimization | ⚠️ Gaps | 1500–2500 | Architecture changes bias! |
| **3: MF → nuclear norm** | Matrix factorization | SVD + spectral theory | ❌ Major gaps | 3000+ | Low-rank bias (strongest) |

---

## Recommended Plan

### Phase 1: Target 1, Option B (Discrete GD → min ℓ₂-norm)
**What to prove:**
```
theorem implicit_l2_bias
  {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
  (hX : X.rank = n) (hnd : n < d) (η : ℝ) (hη : 0 < η ∧ η < 2 / ‖X * X.transpose‖)
  -- w_{k+1} = w_k - η * Xᵀ(Xw_k - y), w_0 = 0
  (w : ℕ → Fin d → ℝ)
  (hw0 : w 0 = 0)
  (hstep : ∀ k, w (k+1) = w k - η • X.transpose.mulVec (X.mulVec (w k) - y)) :
  -- Convergence: w k → X⁺y as k → ∞
  Filter.Tendsto w Filter.atTop (nhds (X.transpose.mulVec ((X * X.transpose).nonsing_inv.mulVec y)))
  -- And this limit is the minimum ℓ₂-norm interpolator
  ∧ ∀ v, X.mulVec v = y → ‖X.transpose.mulVec ((X * X.transpose).nonsing_inv.mulVec y)‖ ≤ ‖v‖ := by
  sorry
```

**Key lemmas to prove:**
1. `row_space_invariant`: w k ∈ row(X) for all k (by induction)
2. `gd_convergence`: w k converges (contraction mapping on the residual)
3. `limit_is_pseudoinverse`: the limit equals Xᵀ(XXᵀ)⁻¹y
4. `pseudoinverse_min_norm`: Xᵀ(XXᵀ)⁻¹y minimizes ‖·‖ among solutions

**New Mathlib infrastructure needed:**
- Pseudoinverse definition and basic properties (could contribute to Mathlib)
- Convergence of linear iteration w_{k+1} = Aw_k + b when ‖A‖ < 1

### Phase 2 (Future): Extend to diagonal linear networks
Build on Phase 1 infrastructure to formalize the ℓ₁ result.

### Phase 3 (Aspirational): Matrix factorization
Would require SVD in Mathlib — a major contribution by itself.

---

## Connection to Existing ArtificialTheorems Work

This formalization complements the existing results:
- **SGD Convergence (Opt/SGD.lean)**: Shows SGD converges for general losses. Our result characterizes *what* it converges to in the overparameterized regime.
- **Universal Approximation (Approx/UniversalApprox.lean)**: Shows neural nets *can* represent any function. Implicit regularization explains why they generalize despite this expressiveness.
- **Value Iteration (RL/)**: Contraction-based convergence arguments similar to what we need for the GD iteration.

The implicit regularization result would be the first formalization in ArtificialTheorems that directly addresses the **generalization mystery** — why overparameterized models trained with GD generalize despite having enough capacity to memorize.

---

## File Structure (Proposed)

```
ArtificialTheorems/
  ImplicitReg/
    MinNormGD.lean          -- Target 1: GD on linear regression → min ℓ₂-norm
    Pseudoinverse.lean      -- Moore-Penrose pseudoinverse basics
ArtificialTheoremsSpec/
  ImplicitReg/
    MinNormGDSpec.lean      -- Formal spec for Target 1
```

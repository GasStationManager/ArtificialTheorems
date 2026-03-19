# ArtificialTheorems: Autoformalization of Theoretical Foundations of AI/ML

This repo is a library of Lean 4 formalizations of theoretical foundations of AI and ML. We explicitly allow and encourage AI-generated / AI-assisted proofs, with the following quality assurance:
- The formal theorem statements (in directory `ArtificialTheoremsSpec/`) are vetted by human experts.
- The proofs (in `ArtificialTheorems/`) are checked using secure verifiers (Comparator, SafeVerify) to ensure that they prove exactly the statements in `ArtificialTheoremsSpec/`.

**Stack:** Lean 4.27.0, Mathlib v4.27.0, SafeVerify, lean4checker.

## Index of Results

| # | Result | File | LOC | Status | Notes |
|---|--------|------|-----|--------|-------|
| 1 | [Universal Approximation (Cybenko 1989)](#1-universal-approximation-theorem-cybenko-1989) | `Approx/UniversalApprox` | 659 | ✅ Proved modulo 1 cited premise | See below |
| 2 | [Robbins–Siegmund Convergence](#2-robbinssiegmund-convergence-theorem) | `Opt/RobbinsSiegmund` | 3980 | ✅ Proved | |
| 3 | [SGD Convergence](#3-sgd-convergence) | `Opt/SGD` | 4016 | ✅ Proved | |
| 4 | [SGD Unique Minimum](#4-sgd-convergence-to-unique-minimum) | `Opt/SGDUniqueMin` | 1753 | ✅ Proved | |
| 5 | [Value Iteration Convergence](#5-value-iteration-convergence) | `RL/ValueIterationComplete` | 407 | ✅ Proved | |
| 6 | [Approximate Value Iteration](#6-approximate-value-iteration) | `RL/ApproxValueIterationInt` | 437 | ✅ Proved | |

**Total: ~11,250 LOC, 6 formalized results, 0 sorrys.**

---

### 1. Universal Approximation Theorem (Cybenko 1989)

**Theorem.** For any continuous sigmoidal σ : ℝ → ℝ and any continuous f : [0,1]ⁿ → ℝ, single-hidden-layer neural networks Σⱼ αⱼ σ(⟨wⱼ, x⟩ + bⱼ) can uniformly approximate f to arbitrary precision on the unit hypercube.

**Reference:** Cybenko, G. "Approximation by Superpositions of a Sigmoidal Function." *Mathematics of Control, Signals, and Systems* 2 (1989): 303–314. [DOI: 10.1007/BF02551274](https://doi.org/10.1007/BF02551274)

**Proof architecture** (all steps fully proved in Lean):
1. **Hahn-Banach density criterion** — if every functional vanishing on a subspace is zero, the subspace is dense
2. **Positive functional → measure bridge** — via Riesz–Markov–Kakutani
3. **Sigmoidal measure uniqueness** — bounded convergence theorem + π-system extensionality
4. **Half-space measure extensionality** — characteristic function uniqueness via 1-d projections
5. **Annihilator triviality** — composing all steps
6. **Main theorem** — density → uniform approximation

**Cited premise (not proved in Lean):** The main theorem assumes `HasJordanDecomposition n` as a hypothesis — that every continuous linear functional on C([0,1]ⁿ, ℝ) is the difference of two positive continuous linear functionals. This is a classical result from functional analysis, verified by [DANA](https://github.com/GasStationManager/DANA) citation research at HIGH confidence:

> **Jordan decomposition of functionals on C(K, ℝ).** Follows from the signed Riesz–Markov–Kakutani representation theorem (every bounded linear functional L on C(K, ℝ) is represented by a signed regular Borel measure ν; Rudin, *Real and Complex Analysis*, 3rd ed., Thm 6.19) composed with the Jordan decomposition of signed measures (ν = ν⁺ − ν⁻; Rudin, Thm 6.12). Equivalently, C(K)* is a Banach lattice (Aliprantis & Border, *Infinite Dimensional Analysis*, 3rd ed., Thms 9.11, 9.14). Not in Mathlib v4.27.0 — no `BanachLattice` class, no signed RMK.

**Files:**
- Spec: [`ArtificialTheoremsSpec/Approx/UniversalApproxSpec.lean`](ArtificialTheoremsSpec/Approx/UniversalApproxSpec.lean)
- Proof: [`ArtificialTheorems/Approx/UniversalApprox.lean`](ArtificialTheorems/Approx/UniversalApprox.lean)

### 2. Robbins–Siegmund Convergence Theorem

**Theorem.** Almost-sure convergence result for nonnegative supermartingales with the Robbins–Siegmund conditions: if (Vₙ) is an adapted nonneg process with E[Vₙ₊₁ | Fₙ] ≤ (1 + αₙ)Vₙ − Uₙ + βₙ where Σαₙ < ∞ and Σβₙ < ∞, then Vₙ converges a.s. and ΣUₙ < ∞ a.s.

**Files:**
- Spec: [`ArtificialTheoremsSpec/Opt/RobbinsSiegmundSpec.lean`](ArtificialTheoremsSpec/Opt/RobbinsSiegmundSpec.lean)
- Proof: [`ArtificialTheorems/Opt/RobbinsSiegmund.lean`](ArtificialTheorems/Opt/RobbinsSiegmund.lean)

### 3. SGD Convergence

**Theorem.** Convergence of stochastic gradient descent: under standard assumptions (Lipschitz gradients, bounded variance, summable step sizes with Σγₙ = ∞, Σγₙ² < ∞), the iterates of SGD converge.

**Files:**
- Spec: [`ArtificialTheoremsSpec/Opt/SGDSpec.lean`](ArtificialTheoremsSpec/Opt/SGDSpec.lean)
- Proof: [`ArtificialTheorems/Opt/SGD.lean`](ArtificialTheorems/Opt/SGD.lean)

### 4. SGD Convergence to Unique Minimum

**Theorem.** Simplified SGD convergence to the unique minimizer under strong convexity assumptions.

**Files:**
- Spec: [`ArtificialTheoremsSpec/Opt/SGDUniqueMinSpec.lean`](ArtificialTheoremsSpec/Opt/SGDUniqueMinSpec.lean)
- Proof: [`ArtificialTheorems/Opt/SGDUniqueMin.lean`](ArtificialTheorems/Opt/SGDUniqueMin.lean)

### 5. Value Iteration Convergence

**Theorem.** Complete convergence of value iteration for discounted MDPs: the Bellman operator is a contraction with factor γ, and iterated application converges to the unique fixed point (optimal value function).

**Files:**
- Spec: [`ArtificialTheoremsSpec/RL/ValueIterationCompleteSpec.lean`](ArtificialTheoremsSpec/RL/ValueIterationCompleteSpec.lean)
- Proof: [`ArtificialTheorems/RL/ValueIterationComplete.lean`](ArtificialTheorems/RL/ValueIterationComplete.lean)

### 6. Approximate Value Iteration

**Theorem.** Error bounds for approximate value iteration: if each iteration incurs at most ε approximation error, the resulting value function stays within a bounded ball of the optimal.

**Files:**
- Spec: [`ArtificialTheoremsSpec/RL/ApproxValueIterationIntSpec.lean`](ArtificialTheoremsSpec/RL/ApproxValueIterationIntSpec.lean)
- Proof: [`ArtificialTheorems/RL/ApproxValueIterationInt.lean`](ArtificialTheorems/RL/ApproxValueIterationInt.lean)

---

## Verification

To verify that the proofs match their specifications, run:

```bash
./scripts/verify.sh
```

This script:
1. Builds both `ArtificialTheorems` and `ArtificialTheoremsSpec`
2. Runs `lean4checker` on all implementation modules to validate the olean files
3. Runs `safe_verify` on each spec/impl pair to ensure the implementations match their specifications exactly

All checks must pass for the proofs to be considered valid.

## Wish List

Contributions are appreciated! Both formal theorem statements vetted by human experts, and autoformalizations of proofs.
I am particularly interested in these areas:

- Universal representation theorems for deep neural nets
- Generalization theory
  - A recent Lean formalization of generalization error bound by Rademacher complexity: https://github.com/auto-res/lean-rademacher
- Implicit regularization (how training via SGD can achieve generalization)
- RL theory
  - A recent Lean formalization of convergence of Q-Learning: https://github.com/ShangtongZhang/rl-theory-in-lean
- Bayesian learning; and perhaps building on top of that, Singular Learning Theory.

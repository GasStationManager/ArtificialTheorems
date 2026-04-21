/-
Proper Scoring Rules — Specification

Gneiting, T. and Raftery, A. E. (2007). "Strictly Proper Scoring Rules, Prediction,
and Estimation." JASA 102(477): 359–378. arXiv:0706.1270.

This file formalizes the binary case (Theorem 4): the correspondence between
(strictly) proper scoring rules and (strictly) convex "generalized entropy"
functions G on [0, 1].

Convention: scoring rules are rewards (higher is better). A scoring rule S is
proper if the forecaster maximizes expected reward by reporting the true
probability. Savage's characterization says proper scoring rules correspond to
convex G; the subgradient construction S(q, o) = G(q) + g(q)·(𝟙[o] - q) gives
the canonical family.
-/

import Mathlib

open Set

noncomputable section

namespace ProperScoring

/-- A (binary) scoring rule: given predicted probability `q` and observed outcome
    `o : Bool`, returns a real-valued reward. -/
abbrev ScoringRule := ℝ → Bool → ℝ

/-- Real-valued indicator of a Bool: true ↦ 1, false ↦ 0. -/
def boolToReal : Bool → ℝ
  | true  => 1
  | false => 0

/-- Expected score when the true probability of `true` is `p` and the forecaster
    reports `q`:  E_p[S(q, O)] = p·S(q, true) + (1 - p)·S(q, false). -/
def expectedScore (S : ScoringRule) (p q : ℝ) : ℝ :=
  p * S q true + (1 - p) * S q false

/-- A scoring rule is proper if truth-telling weakly maximizes expected score
    on [0, 1]. -/
def ProperScoringRule (S : ScoringRule) : Prop :=
  ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1,
    expectedScore S p q ≤ expectedScore S p p

/-- A scoring rule is strictly proper if truth-telling is the *unique* maximizer. -/
def StrictlyProperScoringRule (S : ScoringRule) : Prop :=
  ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1, q ≠ p →
    expectedScore S p q < expectedScore S p p

/-- Generalized entropy associated with `S`:  G(p) := E_p[S(p, O)]. -/
def genEntropy (S : ScoringRule) (p : ℝ) : ℝ := expectedScore S p p

/-! ### Affinity of expected score in the probability argument -/

/-- For fixed `q`, `expectedScore S · q` is affine in the first argument. -/
theorem expectedScore_affine (S : ScoringRule) (q α p₁ p₂ : ℝ) :
    expectedScore S (α * p₁ + (1 - α) * p₂) q
      = α * expectedScore S p₁ q + (1 - α) * expectedScore S p₂ q := by
  sorry

/-- Affine form using two coefficients summing to 1. -/
theorem expectedScore_affine' (S : ScoringRule) (q a b p₁ p₂ : ℝ)
    (hab : a + b = 1) :
    expectedScore S (a * p₁ + b * p₂) q
      = a * expectedScore S p₁ q + b * expectedScore S p₂ q := by
  sorry

/-! ### Tier 1: Proper ⇒ Convex -/

/-- For a proper scoring rule, the generalized entropy is convex on [0, 1]. -/
theorem genEntropy_convexOn (S : ScoringRule) (hS : ProperScoringRule S) :
    ConvexOn ℝ (Icc (0:ℝ) 1) (genEntropy S) := by
  sorry

/-- For a strictly proper scoring rule, the generalized entropy is strictly
    convex on [0, 1]. -/
theorem genEntropy_strictConvexOn (S : ScoringRule)
    (hS : StrictlyProperScoringRule S) :
    StrictConvexOn ℝ (Icc (0:ℝ) 1) (genEntropy S) := by
  sorry

/-- Under the normalization `S(0, false) = 0` and `S(1, true) = 0`, the
    generalized entropy vanishes at the endpoints. -/
theorem genEntropy_boundary_zero (S : ScoringRule)
    (h0 : S 0 false = 0) (h1 : S 1 true = 0) :
    genEntropy S 0 = 0 ∧ genEntropy S 1 = 0 := by
  sorry

/-- Proper + normalization ⇒ generalized entropy is ≤ 0 on [0, 1]. -/
theorem genEntropy_nonpos (S : ScoringRule) (hS : ProperScoringRule S)
    (h0 : S 0 false = 0) (h1 : S 1 true = 0)
    {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    genEntropy S p ≤ 0 := by
  sorry

/-- Strictly proper + normalization ⇒ generalized entropy is < 0 on (0, 1). -/
theorem genEntropy_neg (S : ScoringRule) (hS : StrictlyProperScoringRule S)
    (h0 : S 0 false = 0) (h1 : S 1 true = 0)
    {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    genEntropy S p < 0 := by
  sorry

/-! ### Tier 1b: Savage characterization (convex ⇒ proper) -/

/-- The Savage scoring rule built from a base function `G₀` and a
    (sub)gradient-like function `g`:
        S(q, o) = G₀(q) + g(q) · (𝟙[o] - q).
    When `g q` is a subgradient of a convex `G₀` at `q`, this is the canonical
    family of proper scoring rules associated with `G₀`. -/
def savageRule (G₀ g : ℝ → ℝ) : ScoringRule :=
  fun q o => G₀ q + g q * (boolToReal o - q)

/-- Key identity: expected Savage score at prediction `q` against truth `p`
    equals the tangent-line value of `G₀` at `q`, evaluated at `p`. -/
theorem expectedScore_savageRule (G₀ g : ℝ → ℝ) (p q : ℝ) :
    expectedScore (savageRule G₀ g) p q = G₀ q + g q * (p - q) := by
  sorry

/-- The generalized entropy of a Savage rule equals its base function `G₀`. -/
theorem genEntropy_savageRule (G₀ g : ℝ → ℝ) (p : ℝ) :
    genEntropy (savageRule G₀ g) p = G₀ p := by
  sorry

/-- Savage characterization: if `g` provides the subgradient inequality
    `G₀(q) + g(q)·(p - q) ≤ G₀(p)` throughout [0, 1], then the Savage rule is
    proper. -/
theorem savageRule_proper (G₀ g : ℝ → ℝ)
    (hsub : ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1,
      G₀ q + g q * (p - q) ≤ G₀ p) :
    ProperScoringRule (savageRule G₀ g) := by
  sorry

/-- Strict Savage characterization: a strict subgradient inequality yields a
    strictly proper scoring rule. -/
theorem savageRule_strictlyProper (G₀ g : ℝ → ℝ)
    (hsub : ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1, q ≠ p →
      G₀ q + g q * (p - q) < G₀ p) :
    StrictlyProperScoringRule (savageRule G₀ g) := by
  sorry

/-! ### Tier 2: Brier score -/

/-- The Brier score: S(q, o) = -(q - 𝟙[o])². This is a reward (higher is
    better), with maximum 0 achieved when q matches the outcome exactly. -/
def brier : ScoringRule :=
  fun q o => -(q - boolToReal o) ^ 2

/-- The Brier generalized entropy is G(p) = -p(1 - p). -/
theorem brier_genEntropy (p : ℝ) : genEntropy brier p = -(p * (1 - p)) := by
  sorry

/-- The Brier generalized entropy is strictly convex on [0, 1]. -/
theorem brier_genEntropy_strictConvexOn :
    StrictConvexOn ℝ (Icc (0:ℝ) 1) (genEntropy brier) := by
  sorry

/-- The Brier score is a strictly proper scoring rule. -/
theorem brier_strictlyProper : StrictlyProperScoringRule brier := by
  sorry

end ProperScoring

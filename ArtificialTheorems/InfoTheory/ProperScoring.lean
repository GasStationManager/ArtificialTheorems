/-
Proper Scoring Rules — Proofs

Gneiting, T. and Raftery, A. E. (2007). "Strictly Proper Scoring Rules, Prediction,
and Estimation." JASA 102(477): 359–378. arXiv:0706.1270.

Binary case (Theorem 4): (strictly) proper scoring rules correspond to
(strictly) convex generalized entropy G on [0, 1]. The forward direction uses
that the expected score is affine in p for fixed q — so the "sup of affines"
argument goes through directly from the definition of properness. The reverse
(Savage) direction exhibits the canonical family S(q,o) = G(q) + g(q)(𝟙[o]-q).
-/

import Mathlib

open Set

noncomputable section

namespace ProperScoring

abbrev ScoringRule := ℝ → Bool → ℝ

def boolToReal : Bool → ℝ
  | true  => 1
  | false => 0

@[simp] lemma boolToReal_true : boolToReal true = 1 := rfl
@[simp] lemma boolToReal_false : boolToReal false = 0 := rfl

def expectedScore (S : ScoringRule) (p q : ℝ) : ℝ :=
  p * S q true + (1 - p) * S q false

def ProperScoringRule (S : ScoringRule) : Prop :=
  ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1,
    expectedScore S p q ≤ expectedScore S p p

def StrictlyProperScoringRule (S : ScoringRule) : Prop :=
  ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1, q ≠ p →
    expectedScore S p q < expectedScore S p p

def genEntropy (S : ScoringRule) (p : ℝ) : ℝ := expectedScore S p p

/-! ### Affinity -/

theorem expectedScore_affine (S : ScoringRule) (q α p₁ p₂ : ℝ) :
    expectedScore S (α * p₁ + (1 - α) * p₂) q
      = α * expectedScore S p₁ q + (1 - α) * expectedScore S p₂ q := by
  simp only [expectedScore]
  ring

theorem expectedScore_affine' (S : ScoringRule) (q a b p₁ p₂ : ℝ)
    (hab : a + b = 1) :
    expectedScore S (a * p₁ + b * p₂) q
      = a * expectedScore S p₁ q + b * expectedScore S p₂ q := by
  have hb : b = 1 - a := by linarith
  subst hb
  exact expectedScore_affine S q a p₁ p₂

/-! ### Tier 1: proper ⇒ convex -/

theorem genEntropy_convexOn (S : ScoringRule) (hS : ProperScoringRule S) :
    ConvexOn ℝ (Icc (0:ℝ) 1) (genEntropy S) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro p₁ hp₁ p₂ hp₂ a b ha hb hab
  -- Membership of the convex combination in [0,1]
  have hpmem : a * p₁ + b * p₂ ∈ Icc (0:ℝ) 1 := by
    have h := (convex_Icc (0:ℝ) 1) hp₁ hp₂ ha hb hab
    simpa [smul_eq_mul] using h
  -- Properness at each endpoint against the mixed prediction
  have h₁ : expectedScore S p₁ (a * p₁ + b * p₂) ≤ genEntropy S p₁ :=
    hS p₁ hp₁ (a * p₁ + b * p₂) hpmem
  have h₂ : expectedScore S p₂ (a * p₁ + b * p₂) ≤ genEntropy S p₂ :=
    hS p₂ hp₂ (a * p₁ + b * p₂) hpmem
  -- Affinity collapses the mix to the generalized entropy at the midpoint
  have hmix : genEntropy S (a * p₁ + b * p₂)
            = a * expectedScore S p₁ (a * p₁ + b * p₂)
            + b * expectedScore S p₂ (a * p₁ + b * p₂) := by
    unfold genEntropy
    exact expectedScore_affine' S (a * p₁ + b * p₂) a b p₁ p₂ hab
  show genEntropy S (a • p₁ + b • p₂) ≤ a • genEntropy S p₁ + b • genEntropy S p₂
  simp only [smul_eq_mul]
  calc genEntropy S (a * p₁ + b * p₂)
      = a * expectedScore S p₁ (a * p₁ + b * p₂)
        + b * expectedScore S p₂ (a * p₁ + b * p₂) := hmix
    _ ≤ a * genEntropy S p₁ + b * genEntropy S p₂ := by
        have := mul_le_mul_of_nonneg_left h₁ ha
        have := mul_le_mul_of_nonneg_left h₂ hb
        linarith

theorem genEntropy_strictConvexOn (S : ScoringRule)
    (hS : StrictlyProperScoringRule S) :
    StrictConvexOn ℝ (Icc (0:ℝ) 1) (genEntropy S) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro p₁ hp₁ p₂ hp₂ hne a b ha hb hab
  have hpmem : a * p₁ + b * p₂ ∈ Icc (0:ℝ) 1 := by
    have h := (convex_Icc (0:ℝ) 1) hp₁ hp₂ ha.le hb.le hab
    simpa [smul_eq_mul] using h
  -- The mixed point differs from both endpoints.
  have hp_ne_p₁ : a * p₁ + b * p₂ ≠ p₁ := by
    intro heq
    apply hne
    -- b * p₁ = b * p₂ via (a+b)*p₁ = p₁.
    have hbp : b * p₁ = b * p₂ := by linear_combination -heq + p₁ * hab
    exact mul_left_cancel₀ (ne_of_gt hb) hbp
  have hp_ne_p₂ : a * p₁ + b * p₂ ≠ p₂ := by
    intro heq
    apply hne
    have hap : a * p₁ = a * p₂ := by linear_combination heq - p₂ * hab
    exact mul_left_cancel₀ (ne_of_gt ha) hap
  have h₁ : expectedScore S p₁ (a * p₁ + b * p₂) < genEntropy S p₁ :=
    hS p₁ hp₁ (a * p₁ + b * p₂) hpmem hp_ne_p₁
  have h₂ : expectedScore S p₂ (a * p₁ + b * p₂) < genEntropy S p₂ :=
    hS p₂ hp₂ (a * p₁ + b * p₂) hpmem hp_ne_p₂
  have hmix : genEntropy S (a * p₁ + b * p₂)
            = a * expectedScore S p₁ (a * p₁ + b * p₂)
            + b * expectedScore S p₂ (a * p₁ + b * p₂) := by
    unfold genEntropy
    exact expectedScore_affine' S (a * p₁ + b * p₂) a b p₁ p₂ hab
  show genEntropy S (a • p₁ + b • p₂) < a • genEntropy S p₁ + b • genEntropy S p₂
  simp only [smul_eq_mul]
  calc genEntropy S (a * p₁ + b * p₂)
      = a * expectedScore S p₁ (a * p₁ + b * p₂)
        + b * expectedScore S p₂ (a * p₁ + b * p₂) := hmix
    _ < a * genEntropy S p₁ + b * genEntropy S p₂ := by
        have ha₁ := (mul_lt_mul_iff_of_pos_left ha).mpr h₁
        have hb₁ := (mul_lt_mul_iff_of_pos_left hb).mpr h₂
        linarith

theorem genEntropy_boundary_zero (S : ScoringRule)
    (h0 : S 0 false = 0) (h1 : S 1 true = 0) :
    genEntropy S 0 = 0 ∧ genEntropy S 1 = 0 := by
  refine ⟨?_, ?_⟩ <;> simp [genEntropy, expectedScore, h0, h1]

theorem genEntropy_nonpos (S : ScoringRule) (hS : ProperScoringRule S)
    (h0 : S 0 false = 0) (h1 : S 1 true = 0)
    {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    genEntropy S p ≤ 0 := by
  obtain ⟨hG0, hG1⟩ := genEntropy_boundary_zero S h0 h1
  have hconv := genEntropy_convexOn S hS
  obtain ⟨hp0, hp1⟩ := hp
  have hmem1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := by simp
  have hmem0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := by simp
  have hb : 0 ≤ 1 - p := by linarith
  have hab : p + (1 - p) = 1 := by ring
  have h := hconv.2 hmem1 hmem0 hp0 hb hab
  -- h : genEntropy S (p • 1 + (1-p) • 0) ≤ p • genEntropy S 1 + (1-p) • genEntropy S 0
  have heq1 : p • (1:ℝ) + (1 - p) • (0:ℝ) = p := by simp [smul_eq_mul]
  have heq2 : p • genEntropy S 1 + (1 - p) • genEntropy S 0 = 0 := by
    simp [smul_eq_mul, hG0, hG1]
  rw [heq1, heq2] at h
  exact h

theorem genEntropy_neg (S : ScoringRule) (hS : StrictlyProperScoringRule S)
    (h0 : S 0 false = 0) (h1 : S 1 true = 0)
    {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    genEntropy S p < 0 := by
  obtain ⟨hG0, hG1⟩ := genEntropy_boundary_zero S h0 h1
  have hconv := genEntropy_strictConvexOn S hS
  obtain ⟨hp0, hp1⟩ := hp
  have hmem1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := by simp
  have hmem0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := by simp
  have hne : (1:ℝ) ≠ (0:ℝ) := by norm_num
  have hb : 0 < 1 - p := by linarith
  have hab : p + (1 - p) = 1 := by ring
  have h := hconv.2 hmem1 hmem0 hne hp0 hb hab
  have heq1 : p • (1:ℝ) + (1 - p) • (0:ℝ) = p := by simp [smul_eq_mul]
  have heq2 : p • genEntropy S 1 + (1 - p) • genEntropy S 0 = 0 := by
    simp [smul_eq_mul, hG0, hG1]
  rw [heq1, heq2] at h
  exact h

/-! ### Tier 1b: Savage characterization -/

def savageRule (G₀ g : ℝ → ℝ) : ScoringRule :=
  fun q o => G₀ q + g q * (boolToReal o - q)

theorem expectedScore_savageRule (G₀ g : ℝ → ℝ) (p q : ℝ) :
    expectedScore (savageRule G₀ g) p q = G₀ q + g q * (p - q) := by
  simp only [expectedScore, savageRule, boolToReal_true, boolToReal_false]
  ring

theorem genEntropy_savageRule (G₀ g : ℝ → ℝ) (p : ℝ) :
    genEntropy (savageRule G₀ g) p = G₀ p := by
  unfold genEntropy
  rw [expectedScore_savageRule]
  ring

theorem savageRule_proper (G₀ g : ℝ → ℝ)
    (hsub : ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1,
      G₀ q + g q * (p - q) ≤ G₀ p) :
    ProperScoringRule (savageRule G₀ g) := by
  intro p hp q hq
  rw [expectedScore_savageRule, expectedScore_savageRule]
  have h := hsub p hp q hq
  have hpp : g p * (p - p) = 0 := by ring
  linarith

theorem savageRule_strictlyProper (G₀ g : ℝ → ℝ)
    (hsub : ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1, q ≠ p →
      G₀ q + g q * (p - q) < G₀ p) :
    StrictlyProperScoringRule (savageRule G₀ g) := by
  intro p hp q hq hne
  rw [expectedScore_savageRule, expectedScore_savageRule]
  have h := hsub p hp q hq hne
  have hpp : g p * (p - p) = 0 := by ring
  linarith

/-! ### Tier 2: Brier score -/

def brier : ScoringRule :=
  fun q o => -(q - boolToReal o) ^ 2

theorem brier_genEntropy (p : ℝ) : genEntropy brier p = -(p * (1 - p)) := by
  simp only [genEntropy, expectedScore, brier, boolToReal_true, boolToReal_false]
  ring

theorem brier_genEntropy_strictConvexOn :
    StrictConvexOn ℝ (Icc (0:ℝ) 1) (genEntropy brier) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro p₁ hp₁ p₂ hp₂ hne a b ha hb hab
  show genEntropy brier (a • p₁ + b • p₂) < a • genEntropy brier p₁ + b • genEntropy brier p₂
  simp only [smul_eq_mul, brier_genEntropy]
  -- Identity: a·(-p₁(1-p₁)) + b·(-p₂(1-p₂)) - (-(a p₁ + b p₂)(1 - (a p₁ + b p₂))) = a·b·(p₁-p₂)²
  have hid : a * -(p₁ * (1 - p₁)) + b * -(p₂ * (1 - p₂))
           - (-((a * p₁ + b * p₂) * (1 - (a * p₁ + b * p₂))))
           = a * b * (p₁ - p₂) ^ 2 := by
    linear_combination -(a * p₁ ^ 2 + b * p₂ ^ 2) * hab
  have hsq : 0 < (p₁ - p₂) ^ 2 := by
    have : p₁ - p₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hprod : 0 < a * b * (p₁ - p₂) ^ 2 := by positivity
  linarith [hid, hprod]

theorem brier_strictlyProper : StrictlyProperScoringRule brier := by
  -- brier = savageRule (fun p => -(p*(1-p))) (fun p => 2*p - 1)
  have hEq : brier = savageRule (fun p => -(p * (1 - p))) (fun p => 2 * p - 1) := by
    funext q o
    cases o <;> simp only [brier, savageRule, boolToReal_true, boolToReal_false] <;> ring
  rw [hEq]
  apply savageRule_strictlyProper
  intro p _ q _ hne
  -- Subgradient inequality: -(q*(1-q)) + (2q-1)(p-q) < -(p*(1-p)),
  -- rearranges to (p - q)² > 0.
  have hsq : 0 < (p - q) ^ 2 := by
    have : p - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    positivity
  nlinarith [hsq, sq_nonneg (p - q)]

end ProperScoring

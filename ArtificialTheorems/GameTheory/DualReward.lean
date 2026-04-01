/-
  Dual-Reward Incentive Compatibility for Scoring Rules

  Formalizes the key propositions from the dual-reward mechanism analysis:
  a strictly proper scoring rule with normalization S(0,0) = S(1,1) = 0
  creates incentives for honest reporting and exploitation deterrence.
-/

import Mathlib

open Set

noncomputable section

namespace DualReward

/-- A scoring rule: a function S : [0,1] → {0,1} → ℝ.
    We model this as S : ℝ → Bool → ℝ, with properness conditions
    restricted to the unit interval. -/
structure ScoringRule where
  /-- The scoring function S(q, o) -/
  S : ℝ → Bool → ℝ

/-- The expected score when the true probability is `p` and the report is `q`:
    E_{O ~ Bern(p)}[S(q, O)] = p · S(q, true) + (1 - p) · S(q, false) -/
def ScoringRule.expectedScore (sr : ScoringRule) (p q : ℝ) : ℝ :=
  p * sr.S q true + (1 - p) * sr.S q false

/-- The generalized entropy: G(p) = p · S(p, true) + (1 - p) · S(p, false).
    This is the expected score under honest reporting. -/
def ScoringRule.generalizedEntropy (sr : ScoringRule) (p : ℝ) : ℝ :=
  sr.expectedScore p p

/-- A strictly proper scoring rule with normalization.
    For any p ∈ [0,1], the expected score is uniquely maximized at q = p.
    Additionally, S(0, false) = 0 and S(1, true) = 0. -/
structure StrictlyProperScoringRule extends ScoringRule where
  /-- Strict properness: for p ∈ [0,1] and q ∈ [0,1] with q ≠ p,
      E_{Bern(p)}[S(p, ·)] > E_{Bern(p)}[S(q, ·)] -/
  strictly_proper : ∀ p ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
    q ≠ p → toScoringRule.expectedScore p p > toScoringRule.expectedScore p q
  /-- Normalization: S(0, false) = 0 (predicting 0 when outcome is 0 scores zero) -/
  norm_zero : toScoringRule.S 0 false = 0
  /-- Normalization: S(1, true) = 0 (predicting 1 when outcome is 1 scores zero) -/
  norm_one : toScoringRule.S 1 true = 0

/-- Abbreviation for the generalized entropy of a strictly proper scoring rule -/
abbrev StrictlyProperScoringRule.G (sr : StrictlyProperScoringRule) : ℝ → ℝ :=
  sr.toScoringRule.generalizedEntropy

/-! ## Key Property: Generalized entropy is non-positive -/

/-- G(0) = 0 for a normalized scoring rule. -/
theorem StrictlyProperScoringRule.G_zero (sr : StrictlyProperScoringRule) :
    sr.G 0 = 0 := by sorry

/-- G(1) = 0 for a normalized scoring rule. -/
theorem StrictlyProperScoringRule.G_one (sr : StrictlyProperScoringRule) :
    sr.G 1 = 0 := by sorry

/-- Key Property: For a strictly proper scoring rule with normalization,
    G(p) ≤ 0 for all p ∈ [0,1]. -/
theorem StrictlyProperScoringRule.G_nonpos (sr : StrictlyProperScoringRule)
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    sr.G p ≤ 0 := by sorry

/-- Key Property (strict): G(p) < 0 for p ∈ (0,1). -/
theorem StrictlyProperScoringRule.G_neg (sr : StrictlyProperScoringRule)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    sr.G p < 0 := by sorry

/-- G(p) = 0 iff p ∈ {0, 1}, for p ∈ [0,1]. -/
theorem StrictlyProperScoringRule.G_eq_zero_iff (sr : StrictlyProperScoringRule)
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    sr.G p = 0 ↔ p = 0 ∨ p = 1 := by sorry

/-! ## Proposition 1: Honest Reporting

    For any p ∈ [0,1], the expected score E_{Bern(p)}[S(q, ·)] is uniquely
    maximized at q = p. This is simply a restatement of strict properness. -/

/-- Proposition 1: Honest reporting is uniquely optimal.
    For any true probability p ∈ [0,1] and any alternative report q ≠ p,
    honest reporting yields strictly higher expected score. -/
theorem honest_reporting_optimal (sr : StrictlyProperScoringRule)
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (hpq : q ≠ p) :
    sr.toScoringRule.expectedScore p p > sr.toScoringRule.expectedScore p q := by
  exact sr.strictly_proper p hp q hq hpq

/-! ## Proposition 2: No Distortion

    When both legitimate proving and exploitation are available, legitimate
    proving is strictly preferred for all lam > 0.

    Under legitimate proving: E[R_total] = 1 + λ · 0 = 1
    (since O = 0 a.s., honest report q* = 0, so R_bug = S(0,0) = 0)

    Under exploitation: E[R_total] = 1 + λ · G(f) < 1
    (since G(f) < 0 for f ∈ (0,1))

    Therefore: 1 > 1 + λ · G(f) -/

/-- Proposition 2: No distortion. For any audit rate f ∈ (0,1) and
    any lam > 0, legitimate proving (payoff = 1) strictly dominates
    exploitation (payoff = 1 + λ · G(f)). -/
theorem no_distortion (sr : StrictlyProperScoringRule)
    (f : ℝ) (hf : f ∈ Ioo (0 : ℝ) 1)
    (lam : ℝ) (hlam : lam > 0) :
    (1 : ℝ) > 1 + lam * sr.G f := by sorry

/-! ## Proposition 3: Exploitation Deterrence

    For theorems the agent can exploit but cannot legitimately prove:
    abstaining (payoff = 0) is preferred over exploiting (payoff = 1 + λ · G(f))
    if and only if λ > 1 / |G(f)|. -/

/-- The minimum exchange rate for exploitation deterrence. -/
def lambdaMin (sr : StrictlyProperScoringRule) (f : ℝ) : ℝ :=
  1 / |sr.G f|

/-- Proposition 3: Exploitation deterrence.
    Abstaining (payoff 0) beats exploiting (payoff 1 + λ · G(f))
    if and only if λ > 1/|G(f)|. -/
theorem exploitation_deterrence_iff (sr : StrictlyProperScoringRule)
    (f : ℝ) (hf : f ∈ Ioo (0 : ℝ) 1)
    (lam : ℝ) (hlam : lam > 0) :
    (0 : ℝ) > 1 + lam * sr.G f ↔ lam > lambdaMin sr f := by sorry

/-- Exploitation deterrence (forward direction): if λ > λ_min, then
    abstaining is strictly preferred over exploiting. -/
theorem exploitation_deterrence (sr : StrictlyProperScoringRule)
    (f : ℝ) (hf : f ∈ Ioo (0 : ℝ) 1)
    (lam : ℝ) (hlam : lam > lambdaMin sr f) :
    (0 : ℝ) > 1 + lam * sr.G f := by sorry

/-! ## Main Theorem: Dual-Reward Incentive Compatibility

    Combining Propositions 1-3: for λ > λ_min,
    the unique optimal strategy is to prove legitimately when possible,
    abstain otherwise, and always report honestly. -/

/-- Main Theorem (honest reporting component): For any lam > 0 and any
    true probability p ∈ [0,1], honest reporting uniquely maximizes
    the expected bug-reporting reward. -/
theorem dual_reward_honest_reporting (sr : StrictlyProperScoringRule)
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (hpq : q ≠ p)
    (lam : ℝ) (hlam : lam > 0) :
    lam * sr.toScoringRule.expectedScore p p > lam * sr.toScoringRule.expectedScore p q := by sorry

/-- Main Theorem (no distortion component): For any lam > 0, legitimate
    proving dominates exploitation when both are available. -/
theorem dual_reward_no_distortion (sr : StrictlyProperScoringRule)
    (f : ℝ) (hf : f ∈ Ioo (0 : ℝ) 1)
    (lam : ℝ) (hlam : lam > 0) :
    (1 : ℝ) + lam * 0 > 1 + lam * sr.G f := by sorry

/-- Main Theorem (exploitation deterrence component): For λ > λ_min,
    abstaining dominates exploitation. -/
theorem dual_reward_exploitation_deterrence (sr : StrictlyProperScoringRule)
    (f : ℝ) (hf : f ∈ Ioo (0 : ℝ) 1)
    (lam : ℝ) (hlam : lam > lambdaMin sr f) :
    (0 : ℝ) > 1 + lam * sr.G f := by sorry

end DualReward

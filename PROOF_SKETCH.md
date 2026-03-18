# Universal Approximation Theorem — Proof Sketch (Reformulated)

## Key insight: avoid the signed Riesz representation gap

Mathlib v4.27.0 has:
- ✅ Geometric Hahn-Banach (`geometric_hahn_banach_closed_point`)
- ✅ Positive RMK (`RealRMK.integral_rieszMeasure`): positive linear functional ↔ regular measure
- ✅ Signed measures with Hahn/Jordan decomposition
- ✅ Measure uniqueness on π-systems
- ❌ Full signed Riesz: C(K)* ≅ signed regular Borel measures

**Strategy**: Decompose the functional into positive and negative parts
using the lattice structure of C(K), apply positive RMK to each, then
run Cybenko's measure-theoretic argument on the difference.

## Proof architecture (5 lemmas)

### Lemma 1: `dense_of_dual_annihilator_eq_zero` ✅ (closeable)

**Statement**: If every L ∈ C(Iₙ,ℝ)* vanishing on S is zero, then S is dense.

**Proof**:
1. Suppose S̄ ≠ C(Iₙ,ℝ). Pick g ∉ closure(S).
2. closure(S) is closed. The closure of the span of S is a closed subspace.
   Actually, we need S to be a subspace first. But neuralNetRange isn't a
   subspace — it's just a set.

**Correction**: We need the *span* of neuralNetRange. Or we reformulate:
the closure of neuralNetRange = ⊤.

Actually, looking at the current proof file, `dense_of_dual_annihilator_eq_zero`
works for any set S. The proof:
1. By contradiction: suppose S is not dense, so ∃ g, g ∉ closure(S).
2. closure(S) is closed. Apply `geometric_hahn_banach_closed_point` with
   the closed convex set closure(S) and the point g.
3. Get L ∈ C(Iₙ)* with L(a) < u for all a ∈ closure(S) and u < L(g).
4. Since 0 ∈ closure(S) (assuming S contains the zero function, or we
   handle separately), L(0) < u, so u > 0, so L(g) > 0, hence L ≠ 0.
5. For any s ∈ S: n·s ∈ span(S) ⊆ closure(S) for all n (if S is a subspace).
   Then L(n·s) = n·L(s) < u for all n. This forces L(s) ≤ 0. Similarly
   L(-n·s) = -n·L(s) < u forces L(s) ≥ 0. So L(s) = 0.
6. But hypothesis says L = 0, contradicting L(g) > 0.

**Wait**: This argument needs S to be a subspace (closed under scaling).
neuralNetRange IS closed under addition and scaling (by adjusting α coefficients).
Actually, ∑ αⱼ σ(⟨wⱼ,x⟩+bⱼ) with N neurons — adding two such gives one with
N₁+N₂ neurons, scaling just scales α. So neuralNetRange is a linear subspace.

**Better**: Replace with "dense_of_subspace_annihilator_eq_zero" where S is
known to be a subspace. Then the argument above works cleanly.

**Proof using Mathlib**:
1. Suppose ¬Dense S. Then closure S ≠ ⊤.
2. Pick g ∉ closure S.
3. `geometric_hahn_banach_closed_point` on convex + closed `closure S` vs g.
4. Get f : StrongDual ℝ E with f(a) < u for a ∈ closure S and u < f(g).
5. Since S is a subspace, its closure is too. For s ∈ closure S, n•s ∈ closure S,
   so f(n•s) = n•f(s) < u for all n, forcing f(s) = 0 (and similarly for -s).
6. So f vanishes on S, but f(g) > u > f(0) = 0, so f ≠ 0.
7. By hypothesis, f = 0. Contradiction.

### Lemma 2: `positive_part_functional` (NEW — the bridge)

**Statement**: For L ∈ C(Iₙ,ℝ)*, there exist positive linear functionals
L⁺, L⁻ : C(Iₙ,ℝ) → ℝ such that L = L⁺ - L⁻.

**Proof**: C(K,ℝ) is a Banach lattice. Define:
  L⁺(f) = sup{L(g) : 0 ≤ g ≤ f}  for f ≥ 0
Then extend to all of C(K) by L⁺(f) = L⁺(f⁺) - L⁺((-f)⁺).
Set L⁻ = L⁺ - L.

**This is the hardest new piece.** ~200-300 lines of Lean.
Alternatively: just sorry this and note it as the one gap.

**Alternative**: Check if Mathlib has `Lattice` instance for `ContinuousLinearMap`.
Or `OrderedContinuousLinearMap`. Or `PositiveLinearMap` decomposition.

### Lemma 3: `functional_to_measures` (combines Lemma 2 + positive RMK)

**Statement**: For L ∈ C(Iₙ,ℝ)*, there exist finite Borel measures μ₊, μ₋
on Iₙ such that L(f) = ∫f dμ₊ - ∫f dμ₋ for all f ∈ C(Iₙ,ℝ).

**Proof**: Apply Lemma 2 to get L⁺, L⁻. Apply `RealRMK.rieszMeasure` to
each (they're positive linear functionals, exactly what RMK handles).
Set μ₊ = rieszMeasure(L⁺), μ₋ = rieszMeasure(L⁻).
Then L(f) = L⁺(f) - L⁻(f) = ∫f dμ₊ - ∫f dμ₋.

### Lemma 4: `sigmoidal_measures_agree` (Cybenko's core argument)

**Statement**: If σ is continuous sigmoidal and μ₊, μ₋ are finite Borel
measures on Iₙ with ∫ σ(⟨w,x⟩+b) dμ₊ = ∫ σ(⟨w,x⟩+b) dμ₋ for all w,b,
then μ₊ = μ₋.

**Proof** (the measure-theoretic heart of Cybenko):
1. For fixed w ≠ 0 and any b, ∫ σ(⟨w,x⟩+b) dμ₊ = ∫ σ(⟨w,x⟩+b) dμ₋.
2. Replace b by λb' and send λ → +∞. For x with ⟨w,x⟩ > 0:
   σ(λ⟨w,x⟩ + λb') → 1. For ⟨w,x⟩ < 0: → 0. For ⟨w,x⟩ = 0: σ(λb').
   Actually, better: fix w, replace σ(⟨w,x⟩+b) by σ(λ(⟨w,x⟩+b')) and
   send λ → ∞.
   
   As λ → +∞:
   - If ⟨w,x⟩ > -b': σ(λ(⟨w,x⟩+b')) → 1  (sigmoidal at +∞)
   - If ⟨w,x⟩ < -b': σ(λ(⟨w,x⟩+b')) → 0  (sigmoidal at -∞)
   - If ⟨w,x⟩ = -b': σ(0) (stays at 0)
   
   By BCT (σ is bounded on Iₙ since continuous on compact):
   μ₊({x: ⟨w,x⟩ > -b'}) = μ₋({x: ⟨w,x⟩ > -b'})  (*)
   
   Actually more carefully: we get
   μ₊(H⁺) + σ(0)·μ₊(π) = μ₋(H⁺) + σ(0)·μ₋(π)
   where H⁺ = {⟨w,x⟩ > -b'} and π = {⟨w,x⟩ = -b'}.
   
   Varying b' (the hyperplane slides), and using that hyperplanes have
   measure → 0 as b' varies (at most countably many hyperplanes have
   positive measure), we get (*) for a.e. b'.

   Actually even simpler: the set of half-spaces {x : ⟨w,x⟩ > t} for w ∈ ℝⁿ, t ∈ ℝ
   generates the Borel σ-algebra on Iₙ. They form a π-system. By the
   π-λ theorem (Dynkin), two finite measures agreeing on a π-system that
   generates the σ-algebra must be equal.

3. **Handling the hyperplane term**: We need μ₊ and μ₋ to agree on half-spaces.
   From step 2 with varying b:
   μ₊(H⁺_t) + σ(0)·(μ₊(π_t) - μ₋(π_t)) = μ₋(H⁺_t)
   where H⁺_t = {⟨w,x⟩ > t} and π_t = {⟨w,x⟩ = t}.
   
   But also sending λ → -∞ gives:
   μ₊(H⁻_t) + σ(0)·(μ₊(π_t) - μ₋(π_t)) = μ₋(H⁻_t)... actually no.
   
   Hmm, let me redo. Fix w and vary b freely. We have:
   ∫ σ(⟨w,x⟩ + b) dμ₊ = ∫ σ(⟨w,x⟩ + b) dμ₋  for ALL b.
   
   Now take b = λ·c for fixed c and λ → +∞. Then σ(⟨w,x⟩ + λc).
   If c > 0: this → 1 for all x (since ⟨w,x⟩ is bounded on Iₙ).
   So μ₊(Iₙ) = μ₋(Iₙ). ✓ (total mass agrees)
   
   Now the real trick: replace w by λw (scale the weight, not the bias).
   ∫ σ(λ⟨w,x⟩ + b) dμ₊ = ∫ σ(λ⟨w,x⟩ + b) dμ₋  for all λ, b.
   
   λ → +∞:
   σ(λ⟨w,x⟩ + b) → 1 if ⟨w,x⟩ > 0
   σ(λ⟨w,x⟩ + b) → 0 if ⟨w,x⟩ < 0
   σ(b) if ⟨w,x⟩ = 0
   
   By BCT: μ₊(H⁺_w) + σ(b)·μ₊(π_w) = μ₋(H⁺_w) + σ(b)·μ₋(π_w)
   where H⁺_w = {x ∈ Iₙ : ⟨w,x⟩ > 0} and π_w = {x ∈ Iₙ : ⟨w,x⟩ = 0}.
   
   This holds for ALL b. Since σ is not constant (σ(b) ranges over (0,1)),
   we can vary σ(b) and get two equations:
   - μ₊(H⁺_w) = μ₋(H⁺_w)  (coefficient of the constant term)
   - μ₊(π_w) = μ₋(π_w)      (coefficient of σ(b))
   
   Actually: A + σ(b)·B = 0 for all b, where A = μ₊(H⁺) - μ₋(H⁺)
   and B = μ₊(π) - μ₋(π). Since σ is non-constant, B = 0 and A = 0.
   
   So μ₊ and μ₋ agree on all open half-spaces {⟨w,x⟩ > 0} and hyperplanes
   {⟨w,x⟩ = 0}, hence on all half-spaces {⟨w,x⟩ ≥ 0}, for every w.
   
   More generally (translating): they agree on {⟨w,x⟩ > c} for all w, c
   (by replacing w with w and adjusting the scaling argument).

4. **π-λ theorem**: The collection of half-spaces {⟨w,x⟩ ≤ c} generates
   the Borel σ-algebra on Iₙ (they generate the product topology). Two
   finite measures agreeing on a π-system that generates the σ-algebra
   are equal (Dynkin's theorem).
   
   **Mathlib**: `MeasureTheory.ext_of_generate_finite` or
   `MeasureTheory.Measure.ext_of_generateFrom_of_iUnion`.

### Lemma 5: `universal_approximation_cybenko` (main theorem)

**Statement**: The original theorem.

**Proof**: Compose Lemmas 1-4.
1. Suppose neural net span is not dense.
2. By Lemma 1, ∃ nonzero L vanishing on neural nets.
3. By Lemma 3, L(f) = ∫f dμ₊ - ∫f dμ₋ for measures μ₊, μ₋.
4. L vanishes on neural nets ⟹ ∫ σ(⟨w,x⟩+b) dμ₊ = ∫ σ(⟨w,x⟩+b) dμ₋.
5. By Lemma 4, μ₊ = μ₋, so L = 0. Contradiction.

## What's provable now vs. what needs work

| Lemma | Status | Estimated LOC |
|-------|--------|---------------|
| 1. Hahn-Banach density | ✅ closeable | ~40 |
| 2. Positive decomposition of functionals | ⚠️ hardest new piece | ~200-300 |
| 3. Functional → measures (2 + RMK) | ✅ if 2 done | ~50 |
| 4. Sigmoidal measures agree (BCT + π-λ) | ✅ closeable | ~150-200 |
| 5. Main theorem (composition) | ✅ already done | ~20 |

**The single blocking piece is Lemma 2** (positive decomposition).
Everything else uses existing Mathlib infrastructure.

## Alternative: sorry Lemma 2, prove everything else

If Lemma 2 is too hard, we can:
- State `functional_to_measures` as axiom (sorry'd lemma)
- Prove Lemmas 1, 4, 5 fully
- This leaves one sorry but with clear mathematical justification
- The sorry is a well-known theorem (Riesz decomposition for Banach lattices)
  that could be contributed to Mathlib independently

## Alternative 2: Direct measure formulation

Skip the functional entirely. Reformulate the theorem as:

> If μ is a signed measure on Iₙ and ∫ σ(⟨w,x⟩+b) dμ = 0 for all w,b,
> then μ = 0.

Then the proof is just Lemma 4 (split μ into μ₊, μ₋ via Jordan decomposition,
which IS in Mathlib). This avoids Lemma 2 entirely!

The cost: we need to reformulate `sigmoidal_annihilator_trivial` to work
with signed measures instead of continuous linear functionals. But then
we still need to bridge from Hahn-Banach (which gives a functional) to
signed measures. Same gap.

Unless... we can use that C(K) for compact K is a Banach lattice and
its dual is an order-complete Banach lattice. If Mathlib has this instance,
the decomposition might be automatic.

## Recommended path

1. Check if `ContinuousLinearMap` on `C(K,ℝ)` has a lattice instance in Mathlib
2. If yes: Lemma 2 might be free
3. If no: Sorry Lemma 2, prove everything else (Lemmas 1, 4, 5)
4. File a Mathlib issue/PR for the positive decomposition

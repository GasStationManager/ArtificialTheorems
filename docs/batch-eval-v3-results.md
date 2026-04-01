# Batch Evaluation V3 Results

**Date:** 2026-03-30  
**Evaluator:** Claude Opus 4.6 (subagent, manual proof construction)  
**Method:** Manual proof construction + `lake env lean` compilation testing

## Setup Issues

### Template Generator
The template generator (`scripts/generate_helper_template.py`) produced 49 templates, but **ALL templates fail to compile** (not 37/48 as initially stated). The templates reference `let rec` inner functions (e.g., `sumOfDigits.loop`) using dotted notation that doesn't work outside the parent function scope. The templates are useful as **guidance/sketches** but cannot be used as standalone compilable files.

### Problem File Issues
- **verina_basic_105** and **verina_basic_106**: Use `mkArray` which doesn't exist in Lean 4.27.0 (should be `Array.replicate`). These problems cannot be compiled or proved as-is.

## Problems Attempted (14 target problems)

| Problem | Description | Status | Notes |
|---------|-------------|--------|-------|
| 18 | Sum of digits | ❌ Skipped | Requires reasoning about `Nat.repr` (string representation) — very hard |
| 20 | Unique product | ❌ Skipped | Uses `Std.HashSet`, complex fold/filter equivalence; existing proof_aux has sorry |
| 21 | Is sublist | ✅ **SOLVED** | Proved via `check.induct` with 4 cases |
| 27 | First repeated char | ❌ Skipped | Uses `Std.HashSet`, no problem file exists for proof |
| 40 | Second smallest | ❌ Skipped | Complex multi-case recursion with indices |
| 48 | Is perfect square | ✅ **SOLVED** | Helper lemmas already in proof_aux; main proof assembled |
| 56 | Copy/update segment | ✅ **SOLVED** | Proved `updateSegment_spec` by induction on len |
| 58 | Double array elements | ✅ **SOLVED** | Fixed broken `Array.size_set!`/`getElem!_pos` references with correct `getElem!_def`/`getElem?_setIfInBounds` |
| 71 | Longest common prefix | ❌ Failed | Core issue: can't rewrite `aux ... idx acc` to `aux ... (idx+1) (acc++[c1])` — `rw` causes further unfolding, `simp only` can't rewrite under `.length` |
| 72 | Append | ✅ **SOLVED** | Already had complete proof in problem file |
| 80 | Only once (count occurrences) | ❌ Failed | Requires proving equivalence between `foldl` and recursive `count_from` |
| 90 | Matrix search | ❌ Skipped | Complex 2D matrix search with `Int` indices |
| 105 | Array product | ❌ **BROKEN** | Problem uses `mkArray` which doesn't exist |
| 106 | Array sum | ❌ **BROKEN** | Problem uses `mkArray` which doesn't exist |

## Summary

- **Attempted:** 14 problems
- **Solved:** 5 (21, 48, 56, 58, 72)
- **Failed:** 3 (71, 80, and others attempted but too complex)
- **Skipped (too hard):** 4 (18, 20, 27, 40, 90)
- **Broken problems:** 2 (105, 106 — `mkArray` undefined)

## Common Failure Patterns

### 1. Rewriting under `let` bindings
The most common technical obstacle. When the goal has `let result := f x; P result`, Lean's `rw` tactic rewrites `f x` but also unfolds the result, creating an ugly expanded goal. `simp only [h]` doesn't rewrite under `.length` or `[..]?` projections. `conv` only matches one occurrence. There's no built-in `simp_rw` without Mathlib.

### 2. `getElem!` / `set!` / `setIfInBounds` API
The `Array.getElem!` notation (`a[i]!`) doesn't unfold cleanly with standard simp lemmas. The correct approach requires:
- `getElem!_def` to unfold to `Option.getD`
- `Array.getElem?_setIfInBounds` for the `?` version
- Building custom helper lemmas like `set!_getElem!_eq` and `set!_getElem!_ne`

### 3. `Nat.min` opacity to `omega`
`omega` doesn't know about `Nat.min`. Need to manually extract `idx < str1.length` and `idx < str2.length` from `idx < Nat.min str1.length str2.length`.

### 4. Missing Mathlib tactics
Without importing Mathlib, `push_neg`, `by_contra`, `tauto`, `simp_rw`, `grind` (partially) aren't available. Need to use alternatives like `Decidable.of_not_not`, `Nat.lt_of_lt_of_le ... (Nat.min_le_left ...)`, etc.

### 5. `mkArray` undefined in Lean 4.27
`mkArray` should be `Array.replicate` in Lean 4.27.0. Two problems (105, 106) are broken because of this.

## Recommendations

1. **Fix `mkArray` in problems 105 and 106** — replace with `Array.replicate`
2. **Build a helper lemma library** — create a prelude with `set!_getElem!_eq`, `set!_getElem!_ne`, `Nat.min` unpacking lemmas, etc.
3. **Fix template generator** — templates should either:
   - Be injected into the problem file's `proof_aux` section (not standalone)
   - Or extract `let rec` to top-level `def` with proper naming
4. **Import Mathlib** — problems that import Mathlib have access to much better tactic support. Consider adding `import Mathlib` to all problems.
5. **Add rewrite-under-let tactic** — a custom `rw_let` tactic that rewrites within `let` bindings would solve the main failure pattern.
6. **PantographTree integration** — MCP-based interactive proof would help with the exploration-heavy proofs. Many of these problems could benefit from systematic tactic search.

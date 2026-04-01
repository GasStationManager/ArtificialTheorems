# Loop Invariant Synthesis Pipeline for PantographTree

## Status

**Draft** — design doc for implementation  
**Date:** 2026-03-29  
**Context:** PantographTree solves 50/114 (44%) of Verina benchmark. Nearly all unsolved problems require loop invariant reasoning. This doc designs the pipeline to close that gap.

---

## 1. Problem Analysis

### 1.1 Why Current Search Fails

PantographTree's AND/OR tree search excels at goals closable by decision procedures or shallow structural tactics. Verina problems that need loop invariants fail because:

1. **The main theorem cannot be proved directly** — it requires an auxiliary lemma about a recursive helper function defined in `code_aux`.
2. **The auxiliary lemma must be *invented*, not just applied** — it doesn't exist in the context. The agent must synthesize both the statement and its proof.
3. **The proof structure is deep but formulaic** — induction on the recursion variable, case split, recursive appeal to IH — but current Tier 2 heuristics don't recognize this pattern.

### 1.2 The Three Solved Examples

| Problem | Recursive fn | Helper lemma | Induction scheme | Proof of main thm |
|---------|-------------|-------------|-----------------|-------------------|
| `verina_56` (array copy) | `updateSegment r src sStart dStart n` recurses on `n` | `updateSegment_spec`: full postcondition holds for `updateSegment` | `induction len generalizing dest` | Case split `len=0` vs `len>0`, then `exact updateSegment_spec ...` |
| `verina_74` (max array) | `maxArray_aux a (index+1) new_current` recurses on fuel=`a.size - index` | `maxArray_aux_inv`: result satisfies ∀-bound and ∃-witness | `induction fuel generalizing idx cur` with fuel=`a.size - idx` | `apply maxArray_aux_inv a (a.size-1) 1 a[0]!` with initial invariant witnesses |
| `verina_80` (count once) | `only_once_loop a key (i+1) newCount` recurses on `a.size - i` | `loop_spec`: `only_once_loop a key i c = decide (c + count_from a key i = 1)` | `induction i, c using only_once_loop.induct` | `rw [loop_spec ...]`, `rw [count_occurrences_eq]`, then `simp; omega` |

### 1.3 Extracted Common Pattern

Every loop-invariant proof follows this template:

```
┌─────────────────────────────────────────────────────────┐
│  1. DETECT: main goal mentions a recursive function f   │
│     defined in code_aux                                 │
├─────────────────────────────────────────────────────────┤
│  2. SYNTHESIZE HELPER: state a lemma about f that       │
│     - relates f's output to the postcondition           │
│     - is strong enough to be inductive                  │
│     - generalizes accumulator/state parameters          │
├─────────────────────────────────────────────────────────┤
│  3. PROVE HELPER: by induction on the recursion var     │
│     - Base case: f at base → postcond trivially         │
│     - Step case: unfold f one step, apply IH            │
├─────────────────────────────────────────────────────────┤
│  4. CLOSE MAIN: instantiate helper at initial values    │
│     - apply/exact helper with initial args              │
│     - discharge initial invariant witnesses (omega/simp)│
└─────────────────────────────────────────────────────────┘
```

---

## 2. Pipeline Architecture

### 2.1 Overview

```
                     ┌──────────────┐
                     │  Main Goal   │
                     └──────┬───────┘
                            │
                     ┌──────▼───────┐
                     │   DETECT     │  ← Is there a recursive fn in the goal?
                     └──────┬───────┘
                            │ yes
                     ┌──────▼───────┐
                     │  ANALYZE     │  ← Extract recursion structure
                     └──────┬───────┘
                            │
                     ┌──────▼───────┐
                     │  SYNTHESIZE  │  ← Generate helper lemma candidates
                     └──────┬───────┘
                            │
                    ┌───────▼────────┐
                    │   OR-BRANCH    │  ← Try each candidate
                    │  candidate_1   │
                    │  candidate_2   │
                    │  candidate_3   │
                    └───────┬────────┘
                            │ for each
                    ┌───────▼────────┐
                    │  AND-NODE      │
                    │  ├─ Prove helper│  ← by induction
                    │  └─ Close main │  ← by applying helper
                    └────────────────┘
```

### 2.2 Phase 1: DETECT — Recognizing Loop Invariant Goals

**Trigger condition:** The main theorem's goal, after unfolding definitions, contains a call to a recursive function defined in `code_aux` (or the problem's auxiliary definitions).

**Implementation:**

```python
def detect_loop_invariant_need(goal_state: str, env_info: dict) -> Optional[RecursiveFnInfo]:
    """
    Analyze the current goal to determine if it needs a loop invariant.
    
    Returns RecursiveFnInfo if a recursive function is found, None otherwise.
    """
    # Step 1: Identify function symbols in the goal
    # After `simp only [postcond, code]`, the goal will contain
    # direct calls to recursive functions from code_aux.
    
    # Step 2: For each function symbol, check if it's recursively defined
    # Use pantograph_env_inspect to get the definition and check for
    # self-references in the body.
    
    # Step 3: Extract recursion structure:
    #   - recursion_var: which argument decreases
    #   - base_case: what value triggers the base
    #   - accumulator_args: which args change each iteration
    #   - fixed_args: which args are constant across recursion
    #   - termination_measure: the WF measure (explicit or structural)
```

**Concrete detection heuristics:**

1. **Direct structural recursion** (verina_56 pattern):
   - Function matches on a `Nat` argument: `| 0 => ... | n+1 => ... f ... n ...`
   - Recursion variable: the matched `Nat`
   - Example: `updateSegment r src sStart dStart 0 => r` / `... n+1 => ... updateSegment rNew src sStart dStart n`

2. **Guarded recursion with fuel** (verina_74 pattern):
   - Function has `if index < bound then ... f ... (index + 1) ... else ...`
   - Recursion variable: conceptually `bound - index` (fuel)
   - `termination_by a.size - i` in the definition
   - Example: `maxArray_aux a index current` with `if index < a.size then ... maxArray_aux a (index+1) ...`

3. **Guarded recursion with decidable** (verina_80 pattern):
   - Function has `if h : i < a.size then ... f ... (i+1) ... else ...`
   - Same as (2) but with a decidable proof `h` used for array indexing
   - Example: `only_once_loop a key i keyCount`

**Data structure:**

```python
@dataclass
class RecursiveFnInfo:
    name: str                    # e.g., "updateSegment"
    full_type: str               # the function's type signature
    recursion_var: str           # e.g., "len" or "index"  
    recursion_kind: str          # "structural_nat" | "guarded_ascending" | "well_founded"
    base_value: str              # e.g., "0" or "a.size" (for guard)
    accumulators: list[str]      # args that change: ["r"] or ["current"] or ["keyCount"]
    fixed_args: list[str]        # args that don't change: ["src", "sStart", "dStart"]
    body_base: str               # base case return expression
    body_step: str               # recursive case body
    postcondition: str           # the postcondition from the main theorem
```

### 2.3 Phase 2: ANALYZE — Understanding the Recursion

Once a recursive function is detected, we need deeper analysis to guide invariant synthesis.

**2.3.1 Postcondition decomposition**

Parse the postcondition into atomic properties. Examples:

| Problem | Postcondition | Decomposed |
|---------|--------------|------------|
| verina_56 | `result.size = dest.size ∧ (∀ i, i < dStart → ...) ∧ ...` | 4 conjuncts: size preservation, prefix preservation, suffix preservation, copy correctness |
| verina_74 | `(∀ k, k < a.size → result ≥ a[k]!) ∧ (∃ k, k < a.size ∧ result = a[k]!)` | 2 conjuncts: upper bound, witness |
| verina_80 | `(count = 1 → result) ∧ (count ≠ 1 → ¬result)` | iff between result and count=1 |

**2.3.2 Accumulator-postcondition relationship**

The key insight: **the loop invariant relates the accumulator's current value to the "partial" postcondition**.

| Problem | Accumulator | Invariant meaning |
|---------|------------|-------------------|
| verina_56 | `r` (the array being built) | `r` satisfies the postcondition for the elements copied so far |
| verina_74 | `current` (running max) | `current ≥ a[j]` for all `j < index`, and `current = a[j]` for some `j < index` |
| verina_80 | `keyCount` (running count) | `keyCount + count_from(i) = total_count` — the accumulator plus remaining equals the answer |

**2.3.3 Recursion-to-induction mapping**

| Recursion kind | Induction scheme | Generalized variables |
|---------------|-----------------|----------------------|
| Structural on `n` | `induction n` | All accumulators (e.g., `generalizing dest`) |
| Guarded ascending with fuel | `induction fuel generalizing idx acc` | Index + all accumulators |
| Using `.induct` | `induction idx, acc using f.induct` | Follows function's recursion |

### 2.4 Phase 3: SYNTHESIZE — Generating Helper Lemma Candidates

This is the hardest and most creative step. We generate multiple candidate helper lemma statements and explore them as OR branches.

**2.4.1 Template-based synthesis**

Given `RecursiveFnInfo`, generate the helper lemma template:

```lean
-- Template for structural recursion (verina_56 pattern)
theorem {fn_name}_spec ({fixed_args}) ({rec_var} : Nat) ({acc_args})
    ({preconditions}) :
    {invariant_body} := by
  induction {rec_var} generalizing {acc_args} with
  | zero => {base_proof}
  | succ n ih => {step_proof}
```

```lean
-- Template for guarded ascending recursion (verina_74/80 pattern)
theorem {fn_name}_inv ({fixed_args}) (fuel : Nat) ({index} : Nat) ({acc_args})
    (hfuel : fuel = {bound} - {index}) (hidx : {index} ≤ {bound})
    ({accumulator_invariant_hypotheses}) :
    {conclusion_about_fn_result} := by
  induction fuel generalizing {index} {acc_args} with
  | zero => {base_proof}
  | succ n ih => {step_proof}
```

**2.4.2 Invariant body strategies**

We generate multiple candidate invariant bodies (the `{invariant_body}` slot) as OR branches:

**Strategy A: Direct postcondition lifting** (verina_56 pattern)
- Take the postcondition verbatim and replace `result` with `f(acc_args, rec_var, ...)`
- This works when the recursive function directly computes the final result.

```lean
-- For updateSegment:
-- Postcondition says: result.size = dest.size ∧ ...
-- Helper says: (updateSegment dest src sStart dStart len).size = dest.size ∧ ...
```

**Strategy B: Accumulator-answer relationship** (verina_74 pattern)  
- State that the result of `f` satisfies the postcondition, given that the accumulator currently satisfies a "partial" version.
- The invariant hypotheses become preconditions of the helper.

```lean
-- For maxArray_aux:
-- Helper says: IF current ≥ a[j] for j < idx AND current = a[j] for some j < idx
--              THEN maxArray_aux a idx current ≥ a[k] for all k < a.size
--               AND maxArray_aux a idx current = a[k] for some k < a.size
```

**Strategy C: Equational specification** (verina_80 pattern)
- Define a pure "specification function" that captures what the loop computes.
- State that `f(args) = spec_fn(args)`.
- Then prove `spec_fn` equals the postcondition's notion separately.

```lean
-- For only_once_loop:
-- Define count_from a key i = "count of key in a[i..]"
-- Helper says: only_once_loop a key i c = decide (c + count_from a key i = 1)
-- Separate lemma: count_occurrences a key = count_from a key 0
```

**2.4.3 Candidate ranking**

Order candidates by likelihood:

1. **Strategy A** (direct lifting) — simplest, try first. Works when the recursive function directly builds the result and the postcondition is already stated in terms of the right structure.
2. **Strategy B** (accumulator relationship) — needed when there's a non-trivial accumulator (running max, running sum, etc.). The invariant must capture what the accumulator "means" at each step.
3. **Strategy C** (equational spec) — needed when the postcondition is in terms of a different abstraction (e.g., `foldl` vs recursive loop). Requires synthesizing a specification function.

### 2.5 Phase 4: PROVE — AND/OR Tree Structure

For each candidate helper lemma, we create an AND node with two children:

```
OR: which invariant candidate?
├── Candidate 1 (Strategy A: direct lifting)
│   └── AND:
│       ├── CHILD 1: Prove the helper lemma by induction
│       └── CHILD 2: Close the main theorem using the helper
├── Candidate 2 (Strategy B: accumulator relationship)
│   └── AND:
│       ├── CHILD 1: Prove the helper lemma by induction
│       └── CHILD 2: Close the main theorem using the helper
└── Candidate 3 (Strategy C: equational spec)
    └── AND:
        ├── CHILD 1a: Define the spec function
        ├── CHILD 1b: Prove the helper (loop = spec fn)
        ├── CHILD 1c: Prove spec fn = postcondition's abstraction
        └── CHILD 2: Close the main theorem
```

**2.5.1 Proving the helper (CHILD 1)**

The induction proof follows a mechanical template:

```lean
induction {rec_var} generalizing {accumulators} with
| zero =>  -- or: base case
  -- Unfold the recursive function
  unfold {fn_name}   -- or: simp [{fn_name}]
  -- The goal should now be the invariant with base values
  -- Try Tier 1: simp, omega, simp_all, constructor + simp
  
| succ n ih =>  -- or: step case
  -- Unfold one step of the recursive function
  unfold {fn_name}   -- or: simp only [{fn_name}]
  -- Handle the guard (if present)
  by_cases hlt : {index} < {bound}
  · simp [hlt]
    -- Now the goal mentions f(index+1, new_acc, ...)
    -- Apply IH
    apply ih
    -- Discharge IH's preconditions (the invariant hypotheses for the next step)
    · omega  -- fuel/bound conditions
    · intro j hj  -- universally quantified invariant parts
      by_cases hjidx : j < {index}
      · exact {current_inv} j hjidx  -- inherited from current step
      · have : j = {index} := by omega  -- the new element
        subst this
        {prove_for_new_element}
  · simp [hlt]
    -- At the boundary: function returns accumulator
    exact ⟨{current_invariant_witnesses}⟩
```

**2.5.2 Closing the main theorem (CHILD 2)**

```lean
-- Pattern: unfold postcondition and code, then apply helper
simp only [{postcond_name}, {code_name}]
-- Handle trivial case if present
rcases {precondition_destructure} with ⟨h1, h2, ...⟩
-- For structural recursion (verina_56):
exact {helper_name} {fixed_args} {rec_var} {initial_acc} {precond_witnesses}
-- For guarded recursion (verina_74):
apply {helper_name} {fixed_args} ({bound} - {initial_index}) {initial_index} {initial_acc}
· omega  -- fuel = bound - index
· omega  -- index ≤ bound
· {prove_initial_invariant}  -- e.g., a[0] ≥ a[j] for j < 1
· {prove_initial_witness}    -- e.g., ⟨0, by omega, rfl⟩
```

---

## 3. Implementation Plan

### 3.1 New Components

#### 3.1.1 `LoopDetector` (Phase 1)

**Input:** Goal state string + environment  
**Output:** `Optional[RecursiveFnInfo]`  

**Implementation approach:**
- After the first unfolding (`simp only [postcond, code]`), inspect the goal for function symbols.
- Use `pantograph_env_inspect` on each symbol to retrieve its definition.
- Parse the definition for recursive structure (self-calls in the body).
- Classify the recursion kind and extract the data structure.

**Integration point:** Called as a pre-check before standard Tier 2 tactics. If it returns `Some`, switch to the loop invariant pipeline instead of generic search.

#### 3.1.2 `InvariantSynthesizer` (Phase 3)

**Input:** `RecursiveFnInfo` + postcondition  
**Output:** List of candidate `(helper_statement, induction_scheme, main_proof_sketch)`

**Implementation approach:**
- Template instantiation (mechanical): fill in the templates from §2.4.1 with the extracted recursion info.
- LLM-assisted invariant body generation: for Strategy B and C, use the LLM to propose the invariant body given the recursive function and postcondition as context.
- Candidate deduplication: avoid generating semantically equivalent candidates.

**Key LLM prompt for invariant synthesis:**

```
Given this recursive function:
{fn_definition}

And this postcondition on its result:
{postcondition}

The function recurses on {rec_var}, with accumulators {acc_args}.

What loop invariant relates the accumulators at step {index} to the 
postcondition? The invariant must:
1. Hold at the initial call (when {index} = {initial_value})
2. Be preserved by each recursive step
3. Imply the postcondition when the recursion terminates

State the invariant as a Lean 4 proposition.
```

#### 3.1.3 `InductionProver` (Phase 4, CHILD 1)

**Input:** Helper lemma statement + induction scheme  
**Output:** Proof or failure

This is a specialized sub-search within PantographTree. It uses the existing AND/OR tree but with **induction-aware heuristics**:

1. **First tactic:** Always `induction {rec_var} generalizing {acc_args}`
2. **Base case subgoal:** Try Tier 1 battery aggressively. If that fails, `unfold {fn}` then Tier 1 again.
3. **Step case subgoal:** 
   - `unfold {fn}` or `simp only [{fn}]`
   - Handle guard: `by_cases` or `split`
   - Goal now contains `f(next_args)` — look for IH application
   - `apply ih` with obligation discharge
   - Obligations are typically arithmetic (`omega`) or follow from hypotheses + case analysis

**Depth budget for induction proof:** 15 tactics (higher than normal, since induction proofs are deeper but systematic).

#### 3.1.4 `MainCloser` (Phase 4, CHILD 2)

**Input:** Helper lemma name + main theorem goal  
**Output:** Proof or failure

Simpler than the induction proof. Template:

1. `simp only [{postcond}, {code}]` — unfold definitions
2. Case split if code has trivial branches (e.g., `if len = 0`)
3. `exact helper_name args` or `apply helper_name args` + discharge initial conditions

### 3.2 Integration with AND/OR Tree

The loop invariant pipeline plugs into PantographTree's search as a **macro-tactic** — a single OR node that internally expands into the full structure described in §2.5.

```python
def try_loop_invariant_pipeline(goal_state, env):
    """
    Called when standard Tier 1 + Tier 2 fail.
    Returns an OR-branch node with invariant candidates.
    """
    fn_info = LoopDetector.detect(goal_state, env)
    if fn_info is None:
        return None  # not a loop invariant problem
    
    candidates = InvariantSynthesizer.generate(fn_info)
    
    # Create OR node: try each candidate
    branches = []
    for candidate in candidates:
        # Each candidate becomes an AND node:
        # 1. Have the helper lemma (introduce it via `have`)
        # 2. Close the main goal using the helper
        branch = ANDNode([
            # Sub-problem 1: prove the helper
            HaveTactic(
                name=candidate.helper_name,
                type=candidate.helper_statement,
                proof=InductionProver(candidate)
            ),
            # Sub-problem 2: close main using helper
            MainCloser(candidate)
        ])
        branches.append(branch)
    
    return ORNode(branches)
```

**Lean-level mechanics:** The helper lemma is introduced via `have`:

```lean
-- In the main theorem's proof:
have helper := {helper_statement} := by
  {induction_proof}
-- Now `helper` is in context
{use_helper_to_close}
```

However, this doesn't work well because the `have` block can be very long. **Better approach:** Define the helper as a separate `theorem` in `proof_aux`, then reference it in `proof`.

This means the pipeline must:
1. **Write the helper lemma + proof to `proof_aux`** (the `-- !benchmark @start proof_aux` section)
2. **Write the main proof to `proof`** (the `-- !benchmark @start proof` section)
3. **Verify both type-check together**

This matches exactly what the three examples do.

### 3.3 Two-Phase File Generation

```python
def solve_with_loop_invariant(problem_file, fn_info, candidate):
    """
    1. Generate proof_aux content (helper lemma statement + proof)
    2. Generate proof content (main theorem proof using helper)
    3. Write both to the file
    4. Type-check with Lean
    5. If fails, try next candidate
    """
    # Phase A: write proof_aux
    proof_aux = generate_proof_aux(fn_info, candidate)
    write_section(problem_file, "proof_aux", proof_aux)
    
    # Phase B: write proof  
    proof = generate_main_proof(fn_info, candidate)
    write_section(problem_file, "proof", proof)
    
    # Phase C: verify
    success = lean_check(problem_file)
    if not success:
        # Backtrack: try next candidate or refine current one
        return False
    return True
```

---

## 4. Invariant Synthesis Strategies in Detail

### 4.1 Strategy A: Direct Postcondition Lifting

**When to use:** The recursive function directly computes the result, and the postcondition is already stated in terms that match the function's structure.

**Procedure:**
1. Take each conjunct of the postcondition
2. Replace `result` with `f(initial_acc, fixed_args, rec_var)`
3. The helper states: `∀ rec_var acc, {preconditions on acc} → {postcondition with f(...) for result}`

**Example (verina_56):**

Postcondition:
```lean
result.size = dest.size ∧
(∀ i, i < dStart → result[i]! = dest[i]!) ∧
(∀ i, dStart + len ≤ i → i < result.size → result[i]! = dest[i]!) ∧
(∀ i, i < len → result[dStart + i]! = src[sStart + i]!)
```

Helper (direct lifting — replace `result` with `updateSegment dest src sStart dStart len`):
```lean
theorem updateSegment_spec (src sStart dest dStart len) (hs hd) :
    (updateSegment dest src sStart dStart len).size = dest.size ∧
    (∀ i, i < dStart → (updateSegment dest src sStart dStart len)[i]! = dest[i]!) ∧
    (∀ i, dStart + len ≤ i → ... ) ∧
    (∀ i, i < len → (updateSegment dest src sStart dStart len)[dStart + i]! = src[sStart + i]!)
```

This is literally what verina_56's `updateSegment_spec` is.

### 4.2 Strategy B: Accumulator Invariant with Preconditions

**When to use:** The function has a non-trivial accumulator that carries "partial progress" information. The postcondition can't be stated about the accumulator directly without knowing what's been processed so far.

**Procedure:**
1. Identify what the accumulator "means" at each step (e.g., "max of elements seen so far")
2. State this as preconditions on the helper
3. The helper conclusion is: given these preconditions hold at step `index`, the final result satisfies the postcondition

**Example (verina_74):**

The accumulator is `current : Int`. At step `index`, the invariant is:
- `∀ j, j < index → current ≥ a[j]!` (current is ≥ all seen elements)
- `∃ j, j < index ∧ current = a[j]!` (current equals some seen element)

Helper:
```lean
theorem maxArray_aux_inv (a : Array Int) (fuel idx : Nat) (cur : Int)
    (hfuel : fuel = a.size - idx) (hidx : idx ≤ a.size)
    (hge : ∀ j, j < idx → cur ≥ a[j]!)        -- accumulator invariant part 1
    (hex : ∃ j, j < idx ∧ cur = a[j]!) :        -- accumulator invariant part 2
    (∀ k, k < a.size → maxArray_aux a idx cur ≥ a[k]!) ∧
    (∃ k, k < a.size ∧ maxArray_aux a idx cur = a[k]!) := by ...
```

**Generating the accumulator invariant:**
- For each conjunct `P` of the postcondition, ask: "What does `P` look like restricted to elements `0..index-1`?"
- `∀ k, k < a.size → result ≥ a[k]!` restricted to `0..index-1` → `∀ j, j < index → current ≥ a[j]!`
- `∃ k, k < a.size ∧ result = a[k]!` restricted to `0..index-1` → `∃ j, j < index ∧ current = a[j]!`

This "restriction" operation is the key synthesis step. It can be templated:
- `∀ k, k < BOUND → P(result, k)` → `∀ j, j < index → P(accumulator, j)`
- `∃ k, k < BOUND ∧ P(result, k)` → `∃ j, j < index ∧ P(accumulator, j)`

### 4.3 Strategy C: Equational Specification via Pure Function

**When to use:** The postcondition is stated in terms of a high-level abstraction (e.g., `foldl`, `List.count`, `Array.filter`) that doesn't directly match the recursive function's structure.

**Procedure:**
1. Define a pure specification function `spec_fn` that mirrors the recursive function's structure but computes in a "clean" way
2. Prove: `f(args) = g(spec_fn(args))` where `g` connects spec to postcondition
3. Prove: `spec_fn` relates to the postcondition's abstraction

**Example (verina_80):**

The postcondition uses `count_occurrences a key = a.foldl (fun cnt x => if x = key then cnt + 1 else cnt) 0`.

The recursive function is `only_once_loop a key i keyCount` which doesn't directly relate to `foldl`.

Solution:
1. Define `count_from a key i` — counts occurrences from index `i` onwards (mirrors the loop structure)
2. Prove `loop_spec`: `only_once_loop a key i c = decide (c + count_from a key i = 1)` — by induction
3. Prove `foldl_eq_count_from`: `foldl ... 0 = count_from a key 0` — bridges the two abstractions
4. Main proof: rewrite with both lemmas, then `simp; omega`

**When Strategy C is needed — detection heuristic:**
- The postcondition mentions `foldl`, `foldr`, `map`, `filter`, `count`, or similar higher-order functions
- The code_aux defines a hand-rolled recursive loop that reimplements one of these
- There's a semantic gap between the loop's structure and the spec's structure

### 4.4 Strategy D: Strengthened Invariant (Not in Examples, But Needed)

Sometimes the "obvious" invariant is too weak to be inductive. The step case requires knowing something extra that doesn't appear in the postcondition.

**Example:** A loop that computes array `result` where `result[i] = f(a[i])`. The postcondition says `∀ i, i < n → result[i] = f(a[i])`. But to prove the step case, you also need `result.size = a.size` (to know indexing is valid).

**Procedure:**
1. Try Strategy A first
2. If induction step fails (e.g., can't discharge array bounds), identify what's missing
3. Conjoin the missing property to the invariant
4. Common strengthening properties:
   - Size preservation: `result.size = input.size`
   - Bound on accumulator: `acc ≤ MAX` or `acc ≥ 0`
   - Monotonicity: `acc₁ ≤ acc₂` when `step₁ < step₂`

---

## 5. Edge Cases and Extensions

### 5.1 Nested Loops

When `code_aux` defines two mutually recursive or nested recursive functions (outer loop calls inner loop):

```lean
def outer (a : Array Int) (i : Nat) : Array Int :=
  if i < a.size then
    let row := inner a i 0 0
    outer (a.set! i row) (i + 1)
  else a

def inner (a : Array Int) (i j acc : Nat) : Nat :=
  if j < a.size then inner a i (j + 1) (acc + a[j]!)
  else acc
```

**Approach:** Bottom-up. First prove a helper for `inner`, then use it as a lemma when proving the helper for `outer`.

```
AND node:
├── Prove inner_spec (by induction on a.size - j)
└── Prove outer_spec (by induction on a.size - i, using inner_spec)
```

The `InvariantSynthesizer` should detect nested recursion and generate a sequence of helpers, ordered by dependency.

### 5.2 Multiple Recursive Calls in One Step

Some functions have branching recursion (e.g., quicksort, tree traversal). The induction hypothesis applies to each branch:

```lean
def f (n : Nat) : Nat :=
  if n < 2 then 1
  else f (n - 1) + f (n - 2)
```

**Approach:** Use `induction n using f.induct` which generates the right case split matching the function's definition. The IH gives hypotheses for each recursive call.

### 5.3 `foldl`/`foldr` Equivalence Proofs

When the postcondition uses `foldl` and the code uses a hand-rolled loop (or vice versa), we need a bridging lemma. This is Strategy C.

**Standard bridging pattern:**

```lean
-- Generalized foldl-loop equivalence
theorem foldl_eq_loop (a : Array T) (f : S → T → S) (init : S) (i : Nat) (hi : i ≤ a.size) :
    a.foldl f init i a.size = loop a f i init := by
  induction a.size - i using Nat.strongRecOn generalizing i init with
  | _ n ih =>
    by_cases h : i < a.size
    · rw [Array.foldl_loop h]
      exact ih _ (by omega) _ _ (by omega)
    · have : i = a.size := by omega
      subst this
      simp [Array.foldl_loop, loop]
```

This template can be mechanically instantiated for any `(foldl, loop)` pair.

### 5.4 While-Loop Simulation via Tail Recursion

Verina problems often encode imperative while-loops as tail-recursive functions. The general pattern:

```lean
-- Imperative: while cond do body
-- Lean: def loop state := if cond state then loop (body state) else result state
```

The invariant is always of the form: "if inv(state) holds at this step, then inv(result) holds at termination." This is exactly Strategy B.

### 5.5 Termination Measures

For guarded ascending loops (`if i < bound then ... f (i+1) ... else ...`), the induction must use a fuel argument `fuel = bound - i`. This is because Lean's structural recursion on `Nat` requires a decreasing argument, but `i` is increasing.

**Two approaches:**
1. **Explicit fuel** (verina_74): Add `fuel : Nat` as a parameter and `hfuel : fuel = bound - idx` as a hypothesis. Induct on `fuel generalizing idx acc`.
2. **Function's own induction principle** (verina_80): Use `induction i, acc using f.induct` which automatically handles the well-founded recursion.

Approach (2) is cleaner but requires the function to have a `termination_by` clause that Lean can elaborate into an induction principle. Approach (1) is more robust.

**Recommendation:** Try approach (2) first (`using f.induct`). Fall back to approach (1) if `.induct` isn't available or doesn't work.

---

## 6. Concrete Algorithm

### 6.1 Top-Level Entry Point

```python
def loop_invariant_pipeline(problem: VerinaProblem) -> Optional[Solution]:
    """
    Attempt to solve a Verina problem using loop invariant synthesis.
    Returns (proof_aux_content, proof_content) or None.
    """
    # Step 1: Parse problem structure
    code_aux_fns = parse_code_aux(problem)
    postcondition = parse_postcondition(problem)
    precondition = parse_precondition(problem)
    code_body = parse_code(problem)
    
    # Step 2: Detect recursive functions
    recursive_fns = [fn for fn in code_aux_fns if is_recursive(fn)]
    if not recursive_fns:
        return None  # not a loop invariant problem
    
    # Step 3: Order by dependency (inner loops first)
    recursive_fns = topological_sort(recursive_fns)
    
    # Step 4: For each recursive fn, synthesize invariant candidates
    all_helpers = []
    for fn in recursive_fns:
        fn_info = analyze_recursion(fn)
        candidates = []
        
        # Strategy A: direct lifting
        candidates.append(direct_lifting(fn_info, postcondition))
        
        # Strategy B: accumulator invariant (if fn has accumulators)
        if fn_info.accumulators:
            candidates.append(accumulator_invariant(fn_info, postcondition))
        
        # Strategy C: equational spec (if postcondition uses foldl/foldr/etc)
        if uses_higher_order_spec(postcondition):
            spec_fn = synthesize_spec_function(fn_info)
            candidates.append(equational_spec(fn_info, spec_fn, postcondition))
        
        # Strategy D: LLM-generated (fallback)
        candidates.append(llm_synthesize_invariant(fn_info, postcondition))
        
        all_helpers.append((fn_info, candidates))
    
    # Step 5: Try candidates via OR-branching
    for candidate_combo in product(*[c for _, c in all_helpers]):
        proof_aux = ""
        for (fn_info, _), candidate in zip(all_helpers, candidate_combo):
            # Write helper statement
            proof_aux += candidate.helper_statement + "\n"
            # Attempt induction proof via PantographTree sub-search
            helper_proof = prove_by_induction(candidate)
            if helper_proof is None:
                break  # this candidate failed, try next combo
            proof_aux += helper_proof + "\n"
        else:
            # All helpers proved! Now close the main theorem.
            main_proof = close_main_theorem(all_helpers, candidate_combo, postcondition)
            if main_proof:
                return Solution(proof_aux=proof_aux, proof=main_proof)
    
    return None  # all candidates exhausted
```

### 6.2 Induction Proof Sub-Search

```python
def prove_by_induction(candidate: InvariantCandidate) -> Optional[str]:
    """
    Prove the helper lemma by induction using PantographTree.
    """
    fn_info = candidate.fn_info
    
    # Start proof search for the helper lemma
    proof_search_start(expr=candidate.helper_statement, tree_id="helper")
    
    # Step 1: Set up induction
    if fn_info.recursion_kind == "structural_nat":
        tactic = f"induction {fn_info.recursion_var} generalizing {' '.join(fn_info.accumulators)} with"
    elif fn_info.recursion_kind == "guarded_ascending":
        tactic = f"induction fuel generalizing {fn_info.recursion_var} {' '.join(fn_info.accumulators)} with"
    else:
        tactic = f"induction {fn_info.recursion_var}, {', '.join(fn_info.accumulators)} using {fn_info.name}.induct with"
    
    proof_try_tactic(tactic=tactic)
    
    # Step 2: Handle base case (first subgoal)
    proof_focus_subgoal(goal_index=0)
    # Try: unfold fn, then Tier 1 battery
    try_tactics([
        f"simp [{fn_info.name}]",
        "simp_all",
        "omega",
        f"unfold {fn_info.name}\nsimp_all",
    ])
    proof_subgoal_done()
    
    # Step 3: Handle step case (second subgoal)  
    proof_focus_subgoal(goal_index=1)
    # Unfold the recursive function one step
    proof_try_tactic(tactic=f"simp only [{fn_info.name}]")
    # or: unfold {fn_info.name}
    
    # Handle guard if present
    if fn_info.recursion_kind == "guarded_ascending":
        proof_try_tactic(tactic=f"by_cases hlt : {fn_info.recursion_var} < {fn_info.bound}")
        # Case: guard true → apply IH
        # Case: guard false → at boundary, close with current invariant
    
    # Apply IH and close arithmetic obligations
    # ... (standard PantographTree search with boosted depth)
    
    proof_subgoal_done()
    
    return proof_reconstruct_tactic_proof()
```

---

## 7. Search Budget and Prioritization

### 7.1 When to Invoke the Pipeline

The loop invariant pipeline is **expensive** (multiple proof searches per candidate). Invoke it only when:

1. Standard Tier 1 + Tier 2 search fails within the first 5 minutes
2. A recursive function is detected in the goal (Phase 1 succeeds)
3. The problem hasn't been solved by other means

### 7.2 Budget Allocation

| Phase | Budget |
|-------|--------|
| Detection + Analysis | < 5 seconds (parsing, no search) |
| Candidate generation | < 10 seconds per candidate (template + LLM call) |
| Induction proof per candidate | ≤ 50 tactic attempts, 2 minutes wall time |
| Main theorem closure per candidate | ≤ 20 tactic attempts, 30 seconds |
| Total per problem | ≤ 5 candidates × 2.5 min = 12.5 minutes max |

### 7.3 Early Termination

Abort a candidate if:
- The induction base case doesn't close within 10 tactic attempts (the invariant is probably wrong)
- The step case generates > 5 subgoals after unfolding (too complex, invariant needs strengthening)
- The IH application fails completely (the invariant isn't inductive)

### 7.4 Learning from Failures

When a candidate fails, capture diagnostic information:
- Which subgoal was it stuck on?
- What was the goal state when it failed?
- This information can guide refinement: e.g., if the step case fails because `result.size` is unknown, add a size-preservation conjunct (Strategy D strengthening).

---

## 8. Expected Impact

### 8.1 Coverage Estimate

Of the ~64 unsolved Verina problems:
- **~40 (63%)** are expected to follow the standard patterns (Strategies A-C)
- **~15 (23%)** may need Strategy D (strengthened invariants) or nested loop handling
- **~9 (14%)** may have novel patterns not covered by this pipeline

**Projected solve rate with pipeline:** 50 + 40 = **90/114 (~79%)**, up from 44%.

### 8.2 Implementation Priority

1. **Phase 1: Detection** — straightforward, implement first (1 day)
2. **Phase 3A: Direct lifting** — simplest strategy, covers many problems (2 days)
3. **Phase 4: Induction prover** — the core engine, reusable across strategies (3 days)
4. **Phase 3B: Accumulator invariant** — more complex synthesis (2 days)
5. **Phase 3C: Equational spec** — hardest, needs spec function synthesis (3 days)
6. **Phase 5: Edge cases** — nested loops, strengthening (2 days)

**Total estimated effort:** ~2 weeks of focused implementation.

---

## 9. Open Questions

1. **Helper lemma placement:** Should helpers go in `proof_aux` (file-level) or be introduced via `have` (proof-level)? File-level is cleaner for complex helpers; `have` is more contained. The examples all use `proof_aux`. **Recommendation: `proof_aux`.**

2. **LLM vs template for invariant body:** Templates (Strategies A-C) are reliable but rigid. LLM generation is flexible but may produce unprovable statements. **Recommendation: templates first, LLM as fallback.**

3. **Interaction with `sorry`:** Should the pipeline `sorry` the helper proof to test if the main theorem closes, before investing in the induction proof? **Yes** — this validates the helper statement cheaply before committing to the expensive induction proof.

4. **Incremental invariant strengthening:** When Strategy A fails in the induction step, can we automatically identify what's missing and add it? This is partially possible via goal-state analysis (e.g., if an array bound `i < result.size` can't be proved, add `.size` preservation to the invariant).

5. **Generalization to non-Nat recursion:** Some problems use `List` recursion or tree recursion. The same pipeline applies with different induction schemes (`induction xs with | nil => | cons x xs ih =>`). The templates should be parameterized by the inductive type.

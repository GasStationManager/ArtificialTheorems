#!/usr/bin/env python3
"""
Generate proof_aux helper lemma templates for Verina problems with recursive functions.

Given a Verina problem file with a recursive function in code_aux (or code for let rec),
generates a helper lemma that lifts the postcondition into an inductive lemma about the
recursive function, plus a proof skeleton with sorry.

v2: Uses function.induct instead of fuel-based induction. Detects problem patterns
(fold-matching, copy/build, search) for better invariant generation. Adds push_getElem!
bridge lemmas for Array.push patterns. Better proof skeletons with if_pos/if_neg.

Usage:
    python3 generate_helper_template.py --problem ~/GS/PantographEval/problems/verina_basic_57.lean
    python3 generate_helper_template.py --problems-dir ~/GS/PantographEval/problems/ --targets 57,82,68,69,83,84,94
    python3 generate_helper_template.py --problem FILE --output-dir ./templates/
"""

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

# Import detect_recursive from same directory
SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR))
from detect_recursive import (
    analyze_file,
    extract_section,
    extract_all_sections,
    find_toplevel_defs,
    find_let_rec_defs,
)


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class TemplateContext:
    """All info needed to generate a helper template."""
    problem_id: str
    file_path: str

    # Recursive function info
    fn_name: str
    fn_location: str  # "code_aux" or "code"
    is_let_rec: bool
    parent_function: str  # for let rec, the enclosing def
    parameters: list  # list of {name, type}
    recursion_kind: str
    recursion_var: str
    accumulators: list  # param names that change each call
    fixed_args: list  # param names that stay constant
    termination_measure: str
    raw_definition: str

    # Captured outer vars (for let rec)
    captured_vars: list = field(default_factory=list)

    # Bound expression (for guarded ascending)
    bound_expr: str = ""

    # Postcondition
    postcond_text: str = ""
    postcond_name: str = ""
    postcond_params: list = field(default_factory=list)

    # Main function info
    main_fn_name: str = ""
    main_fn_params: list = field(default_factory=list)
    precond_name: str = ""
    precond_text: str = ""
    code_text: str = ""
    code_aux_text: str = ""

    # Initial call args (how main calls the recursive fn)
    initial_call_args: dict = field(default_factory=dict)

    # Original file text (for name deduplication)
    file_text: str = ""

    # Detected problem pattern for invariant generation
    # One of: "fold_matching", "copy_build", "search", "generic"
    problem_pattern: str = "generic"

    # For fold_matching: the foldl operation expression
    foldl_op_expr: str = ""
    foldl_init_expr: str = ""

    # For copy_build: source expression for each element
    copy_source_expr: str = ""
    copy_start_idx: str = ""

    # For search: the condition being searched for
    search_condition: str = ""
    # Whether the function has a nested if (two guards)
    has_nested_guard: bool = False

    # Whether the recursive call uses Array.push on the accumulator
    uses_array_push: bool = False


# ---------------------------------------------------------------------------
# Analysis helpers
# ---------------------------------------------------------------------------

def extract_postcond_params(text: str) -> tuple[str, list, str]:
    """Extract postcondition name, parameters, and body from file text."""
    # Find the postcond def line first
    def_pattern = r'def\s+(\w+_postcond)\s+((?:\([^)]+\)\s*)+)\s*:?=?'
    m = re.search(def_pattern, text)
    if not m:
        return "", [], ""

    name = m.group(1)
    param_str = m.group(2)

    # Extract the body from the benchmark section
    body = extract_section(text, "postcond")

    # Parse params
    params = []
    for pm in re.finditer(r'\(([^)]+)\)', param_str):
        inner = pm.group(1)
        if ':' in inner:
            names_part, type_part = inner.split(':', 1)
            for n in names_part.strip().split():
                params.append({"name": n.strip(), "type": type_part.strip()})
        else:
            params.append({"name": inner.strip(), "type": None})

    return name, params, body


def extract_precond_info(text: str) -> tuple[str, str]:
    """Extract precondition name and body."""
    pattern = r'def\s+(\w+_precond)\s+'
    m = re.search(pattern, text)
    name = m.group(1) if m else ""

    precond_body = extract_section(text, "precond")
    return name, precond_body


def extract_main_fn_info(text: str) -> tuple[str, list, str]:
    """Extract main function name, params, and how it calls the recursive fn."""
    # Find the main function definition (has h_precond)
    # First find the line with h_precond
    main_line_match = None
    for line in text.split('\n'):
        if re.match(r'\s*def\s+\w+\s.*h_precond\s*:', line) and '_postcond' not in line and '_precond' not in line.split('def')[1].split('(')[0]:
            main_line_match = line
            break

    if not main_line_match:
        # Fallback: find the main function definition without h_precond
        # (some problems have no precondition param)
        for line in text.split('\n'):
            m = re.match(r'\s*def\s+(\w+)\s+((?:\([^)]+\)\s*)*)\s*(?::.*)?:=', line)
            if m and '_precond' not in m.group(1) and '_postcond' not in m.group(1):
                name = m.group(1)
                param_str = m.group(2) or ""
                params = []
                for pm in re.finditer(r'\(([^)]+)\)', param_str):
                    inner = pm.group(1)
                    if ':' in inner:
                        names_part, type_part = inner.split(':', 1)
                        for n in names_part.strip().split():
                            params.append({"name": n.strip(), "type": type_part.strip()})
                return name, params, ""
        return "", [], ""

    # Extract name
    name_m = re.match(r'\s*def\s+(\w+)', main_line_match)
    if not name_m:
        return "", [], ""
    name = name_m.group(1)

    # Extract everything between name and h_precond as params
    between = main_line_match[main_line_match.index(name) + len(name):main_line_match.index('(h_precond')]
    param_str = between.strip()

    # Extract return type (after the h_precond paren, after : and before :=)
    after_precond = main_line_match[main_line_match.index('(h_precond'):]
    ret_m = re.search(r'\)\s*:\s*(.+?)\s*:=', after_precond)
    ret_type = ret_m.group(1).strip() if ret_m else ""

    params = []
    for pm in re.finditer(r'\(([^)]+)\)', param_str):
        inner = pm.group(1)
        if ':' in inner:
            names_part, type_part = inner.split(':', 1)
            for n in names_part.strip().split():
                params.append({"name": n.strip(), "type": type_part.strip()})

    return name, params, ret_type


def _fix_equation_style_params(rec_fn: dict, code_text: str) -> list:
    """Fix parameters for equation-style definitions where detect_recursive misparses."""
    params = rec_fn["parameters"]
    raw_def = rec_fn.get("raw_definition", "")

    # Check if any param has a type that looks like it contains other params
    # e.g., {'name': 'i', 'type': '(oldArr : Array Int) (k : Int) : Nat'}
    needs_fix = False
    for p in params:
        t = p.get("type", "") or ""
        if "(" in t and ":" in t:
            needs_fix = True
            break

    if not needs_fix:
        return params

    # Re-parse: look at the def line in code_text
    fn_name = rec_fn["name"]
    # Find the full def signature
    m = re.search(rf'def\s+{re.escape(fn_name)}\s+(.*?)(?:\n\s*\||:=)', code_text, re.DOTALL)
    if not m:
        return params

    sig = m.group(1).strip()

    # Parse all explicit params first
    new_params = []
    # Extract (name : Type) style params
    for pm in re.finditer(r'\(([^)]+)\)', sig):
        inner = pm.group(1)
        if ':' in inner:
            names_part, type_part = inner.split(':', 1)
            for n in names_part.strip().split():
                n = n.strip()
                if n and re.match(r'^[a-zA-Z_]', n):
                    new_params.append({"name": n, "type": type_part.strip()})

    # Then look at the type signature for additional args
    # e.g., ": Nat → Array Int → Array Int" means two more args
    colon_idx = sig.rfind(':')
    if colon_idx >= 0:
        type_sig = sig[colon_idx + 1:].strip()
        # Split by →
        arrow_types = [t.strip() for t in re.split(r'→', type_sig) if t.strip()]
        # Last type is return type; everything else is an unnamed param
        if len(arrow_types) > 1:
            # Get names from the first equation pattern
            first_eq = re.search(r'\|\s*(.+?)\s*=>', raw_def)
            if first_eq:
                pat_parts = [p.strip() for p in first_eq.group(1).split(',')]
                for i, typ in enumerate(arrow_types[:-1]):
                    if i < len(pat_parts):
                        pname = pat_parts[i].strip()
                        # Clean pattern name
                        if re.match(r'^[a-zA-Z_]\w*$', pname):
                            new_params.append({"name": pname, "type": typ})
                        elif '+' in pname:
                            new_params.append({"name": pname.split('+')[0].strip(), "type": typ})
                        else:
                            new_params.append({"name": f"arg{len(new_params)}", "type": typ})
                    else:
                        new_params.append({"name": f"arg{len(new_params)}", "type": typ})

    return new_params if new_params else params


def _fix_implicit_params(params: list, rec_fn: dict, code_text: str) -> list:
    """Fix parameters when implicit {T : Type} or instance [DecidableEq T] params are present.
    
    detect_recursive treats { and [ as ( which produces garbage like:
    [{'name': 'T', 'type': 'Type'}, {'name': 'DecidableEq', 'type': None}, {'name': 'T', 'type': None}]
    
    We detect this by looking for params with no type or duplicate names, and re-parse
    from source.
    """
    # Quick check: do we have duplicate param names or params with None type?
    names = [p["name"] for p in params]
    has_dupes = len(names) != len(set(names))
    has_none_type = any(p.get("type") is None for p in params)
    
    if not (has_dupes or has_none_type):
        return params
    
    # Re-parse from source code
    fn_name = rec_fn["name"]
    # Find the function definition line with all bracket types
    m = re.search(rf'(?:def|let\s+rec)\s+{re.escape(fn_name)}\s+(.*?)(?::=|\n\s*\|)', code_text, re.DOTALL)
    if not m:
        return params
    
    sig = m.group(1)
    
    new_params = []
    # Parse all param groups: (...), {...}, [...]
    i = 0
    while i < len(sig):
        ch = sig[i]
        if ch == '(':
            # Explicit param
            end = sig.find(')', i)
            if end < 0:
                break
            inner = sig[i+1:end].strip()
            if ':' in inner:
                names_part, type_part = inner.split(':', 1)
                for n in names_part.strip().split():
                    n = n.strip()
                    if n and re.match(r'^[a-zA-Z_]', n):
                        new_params.append({"name": n, "type": type_part.strip()})
            i = end + 1
        elif ch == '{':
            # Implicit param — skip it (don't include in template signature)
            depth = 1
            i += 1
            while i < len(sig) and depth > 0:
                if sig[i] == '{':
                    depth += 1
                elif sig[i] == '}':
                    depth -= 1
                i += 1
        elif ch == '[':
            # Instance param — skip it
            depth = 1
            i += 1
            while i < len(sig) and depth > 0:
                if sig[i] == '[':
                    depth += 1
                elif sig[i] == ']':
                    depth -= 1
                i += 1
        elif ch == ':':
            # Return type annotation — stop parsing params
            break
        else:
            i += 1
    
    return new_params if new_params else params


def _inline_let_bound(bound_expr: str, code_aux: str, code: str) -> str:
    """If bound_expr is a simple identifier that's let-bound, inline its definition."""
    if not bound_expr or not re.match(r'^[a-zA-Z_]\w*$', bound_expr):
        return bound_expr  # Already a complex expression or empty

    # Search for `let <bound_expr> := <value>` in code sections
    for section in [code_aux, code]:
        if not section:
            continue
        m = re.search(rf'let\s+{re.escape(bound_expr)}\s*:=\s*(.+?)(?:\n|$)', section)
        if m:
            result = m.group(1).strip().rstrip(';').strip()
            return result

    return bound_expr


def detect_bound_expr(raw_def: str, rec_var: str) -> str:
    """Extract the bound expression from a guarded ascending recursion."""
    # Match: if rec_var < BOUND then
    pattern = rf'if\s+(?:h\s*:\s*)?{re.escape(rec_var)}\s*<\s*(.+?)\s+then'
    m = re.search(pattern, raw_def)
    if m:
        bound = m.group(1).strip()
        # Clean up trailing punctuation that may be captured (e.g., semicolons)
        bound = bound.rstrip(';').strip()
        return bound
    return ""


class _FakeMatch:
    """Fake regex match object for parent detection."""
    def __init__(self, name, param_str):
        self._groups = (None, name, param_str)
    def group(self, n):
        return self._groups[n]


def _find_parent_def(file_text: str, fn_name: str, has_code_section: bool = True) -> object:
    """Find the parent function definition that contains the let rec.
    
    Returns a match-like object with group(1)=name, group(2)=param_str.
    Handles nested parentheses in type annotations.
    """
    lines = file_text.split('\n')
    
    # Find the line index of the code section start (not code_aux)
    code_start_idx = None
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped == '-- !benchmark @start code':
            code_start_idx = i
            break
    
    if code_start_idx is None:
        return None
    
    # The parent def is the last def before the code section (usually 1-2 lines before)
    # Walk backwards from code section
    for i in range(code_start_idx, -1, -1):
        line = lines[i]
        dm = re.match(r'\s*def\s+(\w+)\s+(.*?)\s*:=\s*$', line)
        if not dm:
            # Try multi-line: def on one line, := at end
            dm = re.match(r'\s*def\s+(\w+)\s+(.*)', line)
            if dm and ':=' not in line:
                # Collect continuation lines until :=
                full_sig = dm.group(2)
                for j in range(i+1, min(i+5, len(lines))):
                    full_sig += ' ' + lines[j].strip()
                    if ':=' in lines[j]:
                        # Remove everything from := onwards
                        full_sig = re.sub(r':=.*', '', full_sig).strip()
                        break
                dname = dm.group(1)
                if '_precond' not in dname and '_postcond' not in dname:
                    return _FakeMatch(dname, full_sig)
                continue
        if dm:
            dname = dm.group(1)
            if '_precond' not in dname and '_postcond' not in dname:
                # Extract just the params part (before return type)
                param_str = dm.group(2)
                # Remove return type (: RetType) and h_precond
                param_str = re.sub(r'\(h_precond[^)]*\)\s*:.*', '', param_str).strip()
                return _FakeMatch(dname, param_str)
    
    return None


def _extract_paren_groups(s: str) -> list:
    """Extract balanced parenthesized groups from a string, handling nested parens.
    
    E.g., "(a : Array (Array Int)) (key : Int)" -> ["a : Array (Array Int)", "key : Int"]
    """
    groups = []
    i = 0
    while i < len(s):
        if s[i] == '(':
            depth = 1
            start = i + 1
            i += 1
            while i < len(s) and depth > 0:
                if s[i] == '(':
                    depth += 1
                elif s[i] == ')':
                    depth -= 1
                i += 1
            if depth == 0:
                groups.append(s[start:i-1].strip())
        else:
            i += 1
    return groups


def _extract_let_rec_own_params(raw_def: str, fn_name: str) -> set:
    """Extract the parameter names of the let rec function itself (for shadowing detection)."""
    own_params = set()
    # Find the let rec line and extract everything up to :=
    m = re.search(
        rf'let\s+rec\s+{re.escape(fn_name)}\s+(.*?):=',
        raw_def, re.DOTALL
    )
    if not m:
        return own_params
    
    sig = m.group(1)
    
    # Extract params from (name : Type) groups
    for pm in re.finditer(r'\(([^)]+)\)', sig):
        inner = pm.group(1)
        if ':' in inner:
            names_part, _ = inner.split(':', 1)
            for n in names_part.strip().split():
                n = n.strip()
                if n and re.match(r'^[a-zA-Z_]\w*$', n):
                    own_params.add(n)
    
    # Also handle match-style params: let rec fn p1 p2 :=
    # Strip out paren groups and return type annotation
    stripped_sig = re.sub(r'\([^)]*\)', '', sig).strip()
    # Remove return type (: Type at end)
    stripped_sig = re.sub(r':\s*\S+\s*$', '', stripped_sig).strip()
    for tok in stripped_sig.split():
        tok = tok.strip()
        if re.match(r'^[a-zA-Z_]\w*$', tok):
            own_params.add(tok)
    
    return own_params


def _extract_let_bindings_before_letrec(source_text: str, fn_name: str, file_text: str = "") -> list:
    """Extract let-bound variables defined before the let rec in the same scope.
    
    These are captured by Lean's closure compilation. Returns list of {name, type}.
    We infer types from the RHS expression where possible.
    """
    let_bindings = []
    lines = source_text.split('\n')
    
    # Find the line with `let rec fn_name`
    letrec_line_idx = None
    for i, line in enumerate(lines):
        if re.search(rf'\blet\s+rec\s+{re.escape(fn_name)}\b', line):
            letrec_line_idx = i
            break
    
    if letrec_line_idx is None:
        return []
    
    # Collect all `let x := expr` before the let rec
    for i in range(letrec_line_idx):
        line = lines[i].strip()
        m = re.match(r'let\s+(\w+)\s*(?::\s*(\S+(?:\s+\S+)*?)\s*)?:=\s*(.+)', line)
        if m:
            name = m.group(1)
            explicit_type = m.group(2)
            rhs = m.group(3).strip().rstrip(';').strip()
            
            if explicit_type:
                inferred_type = explicit_type
            else:
                inferred_type = _infer_type_from_rhs(rhs, file_text)
            
            let_bindings.append({"name": name, "type": inferred_type})
    
    return let_bindings


def _infer_type_from_rhs(rhs: str, file_text: str = "") -> str:
    """Infer a Lean type from a let-binding RHS expression."""
    # Common patterns
    if re.match(r'\w+\.toList\b', rhs):
        # Check if it's String.toList or Array.toList
        var = rhs.split('.')[0]
        if file_text and re.search(rf'\b{re.escape(var)}\s*:\s*String\b', file_text):
            return "List Char"
        return "List _"
    if re.match(r'\w+\.length\b', rhs):
        return "Nat"
    if re.match(r'\w+\.size\b', rhs):
        return "Nat"
    if re.match(r'Nat\.min\b', rhs):
        return "Nat"
    if re.match(r'\w+\.size\s*[\+\-\*]\s*', rhs):
        return "Nat"
    # Array indexing: a[i]! where a : Array T → type is T
    m = re.match(r'(\w+)\[.*\]!?$', rhs)
    if m and file_text:
        var = m.group(1)
        type_m = re.search(rf'\b{re.escape(var)}\s*:\s*(Array\s+\w+)', file_text)
        if type_m:
            arr_type = type_m.group(1)
            # Extract element type from Array T
            elem_m = re.match(r'Array\s+(\w+)', arr_type)
            if elem_m:
                return elem_m.group(1)
    if re.match(r'if\s+', rhs):
        return "_"  # Can't easily infer conditional type
    # Number literals
    if re.match(r'\d+$', rhs):
        return "Nat"
    # String literals
    if rhs.startswith('"'):
        return "String"
    return "_"


def detect_captured_vars(raw_def: str, file_text: str, fn_name: str) -> list:
    """For let rec functions, detect variables captured from enclosing scope.
    
    Handles three sources of captured variables:
    1. Parent function parameters (e.g., def f (a : Array Int) ... let rec loop ...)
    2. Let-bound variables before the let rec (e.g., let n := a.size ... let rec loop ...)
    3. Excludes variables that are SHADOWED by the let rec's own parameters
    """
    captured = []

    # First, determine the let rec's own parameter names (for shadowing check)
    own_params = _extract_let_rec_own_params(raw_def, fn_name)

    # Find the enclosing function definition and source text
    parent_match = None
    source_text = ""  # The full code section containing the let rec

    # Strategy 1: Search in code_aux section (most common for Verina)
    code_aux = extract_section(file_text, "code_aux")
    if code_aux and re.search(rf'let\s+rec\s+{re.escape(fn_name)}\b', code_aux):
        parent_match = re.search(
            rf'def\s+(\w+)\s+((?:\([^)]+\)\s*)*)',
            code_aux
        )
        source_text = code_aux

    # Strategy 2: Search in code section (let rec inside main function)
    if not parent_match:
        code = extract_section(file_text, "code")
        if code and re.search(rf'let\s+rec\s+{re.escape(fn_name)}\b', code):
            # Find the parent def: the function right before "-- !benchmark @start code"
            # This handles nested parens correctly since we parse line by line
            parent_match = _find_parent_def(file_text, fn_name, has_code_section=True)
            source_text = code

    # Extract the let rec body for checking if variables actually appear
    let_rec_body = raw_def
    let_rec_match = re.search(
        rf'let\s+rec\s+{re.escape(fn_name)}\b.*?:=\s*\n(.*)',
        raw_def, re.DOTALL
    )
    if let_rec_match:
        body_after_decl = let_rec_match.group(1)
        lines = body_after_decl.split('\n')
        if lines:
            body_indent = None
            for line in lines:
                stripped = line.lstrip()
                if stripped:
                    body_indent = len(line) - len(stripped)
                    break
            if body_indent is not None:
                body_lines = []
                for line in lines:
                    stripped = line.lstrip()
                    if not stripped:
                        body_lines.append(line)
                        continue
                    indent = len(line) - len(stripped)
                    if indent >= body_indent:
                        body_lines.append(line)
                    else:
                        break
                let_rec_body = '\n'.join(body_lines)

    # Collect candidate captured vars from parent function params
    if parent_match:
        param_str = parent_match.group(2) or ""
        for inner in _extract_paren_groups(param_str):
            if ':' in inner:
                names_part, type_part = inner.split(':', 1)
                for n in names_part.strip().split():
                    n = n.strip()
                    if n == 'h_precond':
                        continue
                    # SHADOWING CHECK: skip if the let rec has its own param with the same name
                    if n in own_params:
                        continue
                    # Check if this name appears in the let rec BODY (not initial call)
                    if re.search(rf'\b{re.escape(n)}\b', let_rec_body):
                        captured.append({"name": n, "type": type_part.strip()})

    # Also collect let-bound variables before the let rec
    if source_text:
        let_bindings = _extract_let_bindings_before_letrec(source_text, fn_name, file_text)
        for lb in let_bindings:
            name = lb["name"]
            # SHADOWING CHECK
            if name in own_params:
                continue
            # Check if this name appears in the let rec body
            if re.search(rf'\b{re.escape(name)}\b', let_rec_body):
                # Don't duplicate if already captured from parent params
                if not any(c["name"] == name for c in captured):
                    captured.append(lb)

    return captured


def detect_initial_call(code_text: str, fn_name: str, is_let_rec: bool) -> dict:
    """Detect how the main function initially calls the recursive function."""
    initial_args = {}

    if is_let_rec:
        # For let rec: the initial call is the LAST standalone call to fn_name
        # that is NOT inside the let rec body (not inside if/then/else)
        # Usually it's the very last line: "count 0 0" or "loop 0 Array.empty"
        pattern = rf'^\s*{re.escape(fn_name)}\s+(.+?)$'
        candidates = []
        in_let_rec = False
        brace_depth = 0
        for line in code_text.strip().split('\n'):
            stripped = line.strip()
            if re.search(rf'let\s+rec\s+{re.escape(fn_name)}\b', stripped):
                in_let_rec = True
                continue
            if in_let_rec:
                # Track whether we're still in the let rec body
                # Simple heuristic: the initial call is at the same or lower indent
                # as the let rec, or after a blank line
                if stripped and not stripped.startswith('if ') and not stripped.startswith('let ') and not stripped.startswith('else') and not stripped.startswith('then') and not stripped.startswith('|'):
                    m = re.search(rf'^{re.escape(fn_name)}\s+(.+)', stripped)
                    if m:
                        candidates.append(m.group(1).strip())
            else:
                m = re.search(rf'{re.escape(fn_name)}\s+(.+?)$', stripped)
                if m and 'def ' not in stripped:
                    candidates.append(m.group(1).strip())

        # The initial call is typically the last candidate
        if candidates:
            initial_args["_raw"] = candidates[-1]
    else:
        # Top-level: look in the code section for calls to fn_name
        pattern = rf'\b{re.escape(fn_name)}\s+(.+?)$'
        for line in code_text.strip().split('\n'):
            line = line.strip()
            m = re.search(pattern, line)
            if m and 'def ' not in line:
                initial_args["_raw"] = m.group(1).strip()
                break

    return initial_args


def detect_problem_pattern(ctx: TemplateContext) -> None:
    """Detect the problem pattern (fold_matching, copy_build, search, generic)
    and populate pattern-specific fields on ctx."""
    postcond = ctx.postcond_text
    raw_def = ctx.raw_definition

    # Check for Array.push usage
    if "acc.push" in raw_def or ".push" in raw_def:
        ctx.uses_array_push = True

    # Check for nested guard (two if-then-else, like linearSearch)
    # Pattern: if BOUND then (if COND then RETURN else RECURSE) else BASE
    nested_if = re.search(
        r'if\s+(?:h\s*:\s*)?\w+\s*<\s*\S+\s+then\s*\n?\s*if\s+',
        raw_def
    )
    if nested_if:
        ctx.has_nested_guard = True

    # 1. Fold-matching: postcondition mentions foldl/foldr
    if "foldl" in postcond or "foldr" in postcond:
        ctx.problem_pattern = "fold_matching"
        # Extract the foldl operation
        foldl_match = re.search(
            r'\.foldl\s*\((fun\s+\w+\s+\w+\s*(?:=>|→)\s*[^)]+)\)\s*(\S+)',
            postcond
        )
        if foldl_match:
            ctx.foldl_op_expr = foldl_match.group(1).strip()
            ctx.foldl_init_expr = foldl_match.group(2).strip()
        return

    # 2. Copy/build: accumulator is Array, uses push, postcondition mentions
    # result.size and result[i]! = source_expr
    acc_types = [p.get("type", "") for p in ctx.parameters if p["name"] in ctx.accumulators]
    has_array_acc = any("Array" in (t or "") for t in acc_types)

    if has_array_acc and ctx.uses_array_push:
        ctx.problem_pattern = "copy_build"
        # Try to extract the source expression from a[i]! pattern in the push call
        push_match = re.search(r'\.push\s*\((.+?)\)', raw_def)
        if push_match:
            ctx.copy_source_expr = push_match.group(1).strip()
        # Detect start index from initial call
        initial_raw = ctx.initial_call_args.get("_raw", "")
        if initial_raw:
            parts = _tokenize_lean_args(initial_raw)
            # The recursion var position in params
            for idx_p, p in enumerate(ctx.parameters):
                if p["name"] == ctx.recursion_var and idx_p < len(parts):
                    ctx.copy_start_idx = parts[idx_p]
                    break
        return

    # 3. Search: no accumulator, postcondition mentions result < bound and
    # some element equality/condition, plus ∀ k < result → ¬cond
    if not ctx.accumulators and ctx.has_nested_guard:
        # Extract the search condition from the inner if
        # Try multiple patterns since the return value after `then` can be multi-word
        body_lines = raw_def.split('\n', 2)[-1] if '\n' in raw_def else raw_def
        
        # Pattern 1: if COND then EXPR else RECURSE (single line)
        inner_if = re.search(
            r'if\s+(?:h\s*:\s*)?(.+?)\s+then\s+.+?\s+else\s+(?:\w+)',
            body_lines
        )
        if inner_if:
            ctx.search_condition = inner_if.group(1).strip()
        
        # Only use search pattern if we successfully extracted a condition
        if ctx.search_condition:
            ctx.problem_pattern = "search"
            return
        # Otherwise fall through to generic

    ctx.problem_pattern = "generic"


def refine_accumulators(ctx: TemplateContext, file_text: str):
    """Improve accumulator detection by checking the recursive call more carefully."""
    raw = ctx.raw_definition
    fn_name = ctx.fn_name

    # Find the recursive call line
    rec_call_pattern = rf'\b{re.escape(fn_name)}\s+'
    rec_lines = []
    for line in raw.split('\n'):
        stripped = line.strip()
        # Skip the definition line itself
        if stripped.startswith('def ') or stripped.startswith('let rec '):
            continue
        if re.search(rec_call_pattern, stripped):
            rec_lines.append(stripped)

    if not rec_lines:
        return

    # Take the first recursive call
    rec_line = rec_lines[0]

    # Extract arguments from the recursive call
    m = re.search(rf'\b{re.escape(fn_name)}\s+(.+?)(?:\n|$)', rec_line)
    if not m:
        return

    args_str = m.group(1).strip()

    # Tokenize (simple: split by space, respecting parens)
    tokens = _tokenize_lean_args(args_str)

    # Map to parameter positions
    param_names = [p["name"] for p in ctx.parameters]
    accumulators = []
    fixed = []

    for i, param in enumerate(param_names):
        if param == ctx.recursion_var:
            continue
        if i < len(tokens):
            tok = tokens[i]
            # If the token is just the param name, it's fixed
            if tok == param:
                fixed.append(param)
            else:
                accumulators.append(param)
        else:
            # Can't determine, assume accumulator
            accumulators.append(param)

    # For captured vars in let rec, they're always fixed
    for cv in ctx.captured_vars:
        if cv["name"] in accumulators:
            accumulators.remove(cv["name"])
            if cv["name"] not in fixed:
                fixed.append(cv["name"])

    ctx.accumulators = accumulators
    ctx.fixed_args = fixed


def _tokenize_lean_args(s: str) -> list:
    """Simple tokenizer for Lean function call arguments."""
    tokens = []
    depth = 0
    current = ""
    for ch in s:
        if ch in '([{':
            depth += 1
            current += ch
        elif ch in ')]}':
            depth -= 1
            current += ch
        elif ch == ' ' and depth == 0:
            if current.strip():
                tokens.append(current.strip())
            current = ""
        else:
            current += ch
    if current.strip():
        tokens.append(current.strip())
    return tokens


# ---------------------------------------------------------------------------
# Build template context
# ---------------------------------------------------------------------------

def build_context(file_path: Path) -> Optional[TemplateContext]:
    """Build a TemplateContext from a problem file."""
    text = file_path.read_text()
    problem_id = file_path.stem

    # Run detect_recursive analysis
    analysis = analyze_file(file_path)
    if not analysis.has_recursive_functions:
        return None

    # Take the first (or most relevant) recursive function
    rec_fn = analysis.recursive_functions[0]

    sections = extract_all_sections(text)
    postcond_name, postcond_params, postcond_text = extract_postcond_params(text)
    precond_name, precond_text = extract_precond_info(text)
    main_fn_name, main_fn_params, _ = extract_main_fn_info(text)

    ctx = TemplateContext(
        problem_id=problem_id,
        file_path=str(file_path),
        fn_name=rec_fn["name"],
        fn_location=rec_fn["location"],
        is_let_rec=rec_fn.get("is_let_rec", False),
        parent_function=rec_fn.get("parent_function", ""),
        parameters=rec_fn["parameters"],
        recursion_kind=rec_fn["recursion_kind"],
        recursion_var=rec_fn.get("recursion_var", ""),
        accumulators=rec_fn.get("accumulators", []),
        fixed_args=rec_fn.get("fixed_args", []),
        termination_measure=rec_fn.get("termination_measure", ""),
        raw_definition=rec_fn.get("raw_definition", ""),
        postcond_text=postcond_text,
        postcond_name=postcond_name,
        postcond_params=postcond_params,
        main_fn_name=main_fn_name,
        main_fn_params=main_fn_params,
        precond_name=precond_name,
        precond_text=precond_text,
        code_text=sections.get("code", ""),
        code_aux_text=sections.get("code_aux", ""),
    )

    # Store original file text for name deduplication
    ctx.file_text = text

    # Fix params for equation-style definitions (detect_recursive may misparse these)
    ctx.parameters = _fix_equation_style_params(rec_fn, ctx.code_aux_text or sections.get("code", ""))

    # Fix implicit/instance params: {T : Type} [DecidableEq T] are misparsed by detect_recursive
    # Re-parse from source if we detect type-class-like params
    ctx.parameters = _fix_implicit_params(ctx.parameters, rec_fn, ctx.code_aux_text or sections.get("code", ""))

    # Detect bound expression
    if ctx.recursion_var:
        ctx.bound_expr = detect_bound_expr(rec_fn.get("raw_definition", ""), ctx.recursion_var)
    else:
        ctx.bound_expr = ""

    # If bound_expr is a local let-binding, try to inline it
    ctx.bound_expr = _inline_let_bound(ctx.bound_expr, sections.get("code_aux", ""), sections.get("code", ""))

    # Detect captured vars for let rec
    if ctx.is_let_rec:
        ctx.captured_vars = detect_captured_vars(ctx.raw_definition, text, ctx.fn_name)

    # Detect initial call — always look in the code section for the initial call
    # For code_aux functions: the initial call is in the code section
    # For code let-rec functions: the initial call is also in the code section (after the let rec)
    code_for_initial = sections.get("code", "")
    if ctx.is_let_rec and ctx.fn_location == "code_aux":
        # For let rec in code_aux, look at the end of code_aux for the initial call
        code_for_initial = sections.get("code_aux", "")
    elif not ctx.is_let_rec and ctx.fn_location == "code_aux":
        # Top-level code_aux fn: the main function calls it from the code section
        code_for_initial = sections.get("code", "")
    ctx.initial_call_args = detect_initial_call(code_for_initial, ctx.fn_name, ctx.is_let_rec)

    # Refine accumulator detection
    refine_accumulators(ctx, text)

    # Detect problem pattern
    detect_problem_pattern(ctx)

    return ctx


# ---------------------------------------------------------------------------
# Template generation
# ---------------------------------------------------------------------------

def _deduplicate_name(name: str, file_text: str) -> str:
    """If `name` already exists as a theorem/lemma/def in file_text, append suffix to avoid clash."""
    candidate = name
    suffix_num = 0
    while re.search(rf'\b(theorem|lemma|def|private\s+theorem|private\s+lemma)\s+{re.escape(candidate)}\b', file_text):
        suffix_num += 1
        if suffix_num == 1:
            candidate = name + "_aux"
        else:
            candidate = name + f"_aux{suffix_num}"
    return candidate


def generate_template(ctx: TemplateContext) -> str:
    """Generate the full proof_aux template for a problem."""
    if ctx.recursion_kind == "guarded_ascending":
        return _gen_guarded_ascending(ctx)
    elif ctx.recursion_kind == "structural_nat":
        return _gen_structural_nat(ctx)
    elif ctx.recursion_kind in ("guarded_descending",):
        return _gen_guarded_descending(ctx)
    elif ctx.recursion_kind == "structural_list":
        return _gen_structural_list(ctx)
    else:
        return _gen_generic(ctx)


def _param_sig(params: list, exclude: list = None) -> str:
    """Format parameters as Lean signature."""
    exclude = exclude or []
    parts = []
    for p in params:
        if p["name"] in exclude:
            continue
        if p.get("type"):
            parts.append(f"({p['name']} : {p['type']})")
        else:
            parts.append(f"({p['name']})")
    return " ".join(parts)


def _build_postcond_lifted(ctx: TemplateContext) -> str:
    """
    Lift the postcondition to work for arbitrary starting index/accumulator.

    This is the core creative step. We generate the postcondition body with
    `result` replaced by the recursive function call.
    """
    postcond = ctx.postcond_text

    # Build the function call expression
    fn_call = _build_fn_call(ctx)

    # The postcondition typically has `result` as a variable
    # We want to substitute result -> fn_call
    # But we also need to be careful: postcondition might reference the main fn params,
    # not the recursive fn params.

    # For simple cases, just replace result with fn_call
    lifted = postcond.replace("result", fn_call)

    return lifted


def _build_fn_call(ctx: TemplateContext) -> str:
    """Build the function call expression for the recursive function."""
    qualified_name = _get_qualified_name(ctx)
    if ctx.is_let_rec:
        parts = []
        # Captured vars first (they're the outer function's params)
        for cv in ctx.captured_vars:
            parts.append(cv["name"])
        # Then the recursive fn's own params
        for p in ctx.parameters:
            parts.append(p["name"])
        return f"({qualified_name} {' '.join(parts)})"
    else:
        parts = []
        for p in ctx.parameters:
            parts.append(p["name"])
        return f"({qualified_name} {' '.join(parts)})"


def _gen_guarded_ascending(ctx: TemplateContext) -> str:
    """Generate template for guarded ascending recursion (if i < bound then ... f (i+1) ...).

    Uses function.induct instead of fuel-based induction.
    Dispatches to pattern-specific invariant generation.
    """
    # Dispatch to pattern-specific generators
    if ctx.problem_pattern == "fold_matching":
        return _gen_fold_matching(ctx)
    elif ctx.problem_pattern == "copy_build":
        return _gen_copy_build(ctx)
    elif ctx.problem_pattern == "search":
        return _gen_search(ctx)
    else:
        return _gen_guarded_ascending_generic(ctx)


def _get_qualified_name(ctx: TemplateContext) -> str:
    """Get the qualified name for a recursive function.

    For let rec functions, traces the full nesting path.
    E.g., main_fn.outer.inner for a doubly-nested let rec.
    """
    fn_name = ctx.fn_name
    if ctx.is_let_rec:
        # Determine the root (enclosing def)
        root = ""
        source_text = ""
        if ctx.fn_location == "code_aux":
            m = re.search(r'def\s+(\w+)', ctx.code_aux_text)
            if m:
                root = m.group(1)
            source_text = ctx.code_aux_text
        elif ctx.fn_location == "code":
            root = ctx.main_fn_name or ""
            # Fallback: find the enclosing def from file text if main_fn_name is empty
            if not root:
                # Look for def that contains the let rec in the code section
                m = re.search(r'def\s+(\w+)(?:\s|\()', ctx.file_text)
                if m and m.group(1) not in (ctx.precond_name, ctx.postcond_name):
                    # Find the main function def (not precond/postcond)
                    for dm in re.finditer(r'def\s+(\w+)(?:\s|\()', ctx.file_text):
                        dname = dm.group(1)
                        if '_precond' not in dname and '_postcond' not in dname and dname != ctx.fn_name:
                            root = dname
                            break
            source_text = ctx.code_text

        if root and source_text:
            # Find all let rec definitions and build nesting chain
            # by tracking which let recs enclose our target fn
            chain = _trace_let_rec_nesting(source_text, fn_name, root)
            if chain:
                return chain

        if root:
            return f"{root}.{fn_name}"
    return fn_name


def _trace_let_rec_nesting(source_text: str, target_fn: str, root_name: str) -> str:
    """Trace the full nesting path for a let rec function.

    Returns e.g. 'root.outer.inner' for nested let recs.
    """
    lines = source_text.split('\n')
    # Find all let rec definitions with their line positions and indentation
    let_recs = []
    for i, line in enumerate(lines):
        m = re.match(r'^(\s*)let\s+rec\s+(\w+)', line)
        if m:
            indent = len(m.group(1))
            name = m.group(2)
            let_recs.append((i, indent, name))

    if not let_recs:
        return f"{root_name}.{target_fn}"

    # Find the target
    target_line = None
    target_indent = None
    for i, indent, name in let_recs:
        if name == target_fn:
            target_line = i
            target_indent = indent
            break

    if target_line is None:
        return f"{root_name}.{target_fn}"

    # Build the chain: walk backwards from target, collecting enclosing let recs
    # A let rec at a LOWER indent that appears BEFORE the target is an enclosing scope
    chain = [target_fn]
    current_indent = target_indent
    for i, indent, name in reversed(let_recs):
        if i >= target_line:
            continue
        if indent < current_indent:
            chain.append(name)
            current_indent = indent

    chain.append(root_name)
    chain.reverse()
    return ".".join(chain)


def _build_call_args(ctx: TemplateContext) -> list:
    """Build the argument list for calling the recursive function."""
    call_args = []
    if ctx.is_let_rec:
        for cv in ctx.captured_vars:
            call_args.append(cv["name"])
    for p in ctx.parameters:
        call_args.append(p["name"])
    return call_args


def _build_induct_clause(ctx: TemplateContext, qualified_name: str) -> str:
    """Build the induction clause using function.induct.

    For let rec inside parent g: use g.f.induct
    For top-level: use f.induct
    Induction args: recursion_var, accumulators
    For let rec with captured vars, specify them with (var := var) syntax.
    """
    rec_var = ctx.recursion_var
    acc_names = ctx.accumulators

    induct_args = [rec_var] + acc_names
    induct_clause = f"induction {', '.join(induct_args)} using {qualified_name}.induct"

    # For let rec, pass captured vars explicitly
    if ctx.is_let_rec and ctx.captured_vars:
        captured_bindings = " ".join(
            f"({cv['name']} := {cv['name']})" for cv in ctx.captured_vars
        )
        induct_clause += f" {captured_bindings}"
    # For top-level functions, pass fixed args explicitly
    elif not ctx.is_let_rec and ctx.fixed_args:
        fixed_bindings = " ".join(
            f"({name} := {name})" for name in ctx.fixed_args
        )
        induct_clause += f" {fixed_bindings}"

    return induct_clause


def _gen_fold_matching(ctx: TemplateContext) -> str:
    """Generate template for fold-matching pattern.

    The helper relates the recursive function to List.foldl over array.toList.drop i.
    Example: count i acc = (numbers.toList.drop i).foldl f acc
    """
    lines = []

    qualified_name = _get_qualified_name(ctx)
    rec_var = ctx.recursion_var
    bound = ctx.bound_expr
    call_args = _build_call_args(ctx)
    fn_call_raw = f"{qualified_name} {' '.join(call_args)}"
    fn_call_expr = f"({fn_call_raw})" if ' ' in fn_call_raw else fn_call_raw
    induct_clause = _build_induct_clause(ctx, qualified_name)

    # Identify the array and foldl operation
    # Use the captured vars or fixed args to find the array
    array_name = ""
    for cv in ctx.captured_vars:
        if "Array" in (cv.get("type", "") or ""):
            array_name = cv["name"]
            break
    if not array_name:
        for p in ctx.parameters:
            if "Array" in (p.get("type", "") or "") and p["name"] in ctx.fixed_args:
                array_name = p["name"]
                break
    if not array_name:
        array_name = "arr"  # fallback

    foldl_op = ctx.foldl_op_expr or "fun acc x => sorry"
    acc_name = ctx.accumulators[0] if ctx.accumulators else "acc"

    helper_name = f"{ctx.fn_name}_eq_list_foldl"
    helper_name = _deduplicate_name(helper_name, ctx.file_text)

    # Build parameter signature
    sig_parts = []
    for cv in ctx.captured_vars:
        sig_parts.append(f"({cv['name']} : {cv.get('type', '_')})")
    for p in ctx.parameters:
        sig_parts.append(f"({p['name']} : {p.get('type', '_')})")
    sig_parts.append(f"(h{rec_var} : {rec_var} ≤ {bound})")
    param_sig = " ".join(sig_parts)

    lines.append(f"-- Helper lemma for {qualified_name} (fold-matching pattern)")
    lines.append(f"-- The loop computes ({array_name}.toList.drop {rec_var}).foldl f {acc_name}")
    lines.append(f"-- Proof sketch: {induct_clause}")
    lines.append(f"--   case guard-true: unfold, rewrite drop as cons, bridge getElem!, apply ih")
    lines.append(f"--   case guard-false: unfold, drop is nil, foldl nil = acc")
    lines.append(f"theorem {helper_name} {param_sig} :")
    lines.append(f"    {fn_call_expr} =")
    lines.append(f"    ({array_name}.toList.drop {rec_var}).foldl ({foldl_op}) {acc_name} := by")
    lines.append(f"  sorry")

    lines.append("")
    lines.append(f"-- Main proof: use {helper_name} at initial values, then bridge with Array.foldl_toList")
    lines.append(f"-- In the main proof section, use:")
    lines.append(f"--   simp only [{ctx.postcond_name}, {ctx.main_fn_name}]")

    if ctx.fn_location == "code_aux":
        parent_name = qualified_name.split('.')[0] if '.' in qualified_name else ctx.main_fn_name
        lines.append(f"--   simp only [{parent_name}]  -- or: unfold {parent_name}")

    lines.append(f"--   rw [{helper_name} ... 0 {ctx.foldl_init_expr or '0'} (by omega)]")
    lines.append(f"--   simp only [List.drop_zero]")
    lines.append(f"--   rw [Array.foldl_toList]  -- NOT Array.foldl_loop (doesn't exist in Lean 4.27)")
    lines.append(f"--   omega")

    return "\n".join(lines)


def _gen_copy_build(ctx: TemplateContext) -> str:
    """Generate template for copy/build pattern (accumulator builds an array via push).

    Includes push_getElem! bridge lemmas as standard boilerplate.
    Invariant: acc.size = i - startIdx ∧ ∀ j < acc.size, acc[j]! = source_expr
    """
    lines = []

    qualified_name = _get_qualified_name(ctx)
    rec_var = ctx.recursion_var
    bound = ctx.bound_expr
    call_args = _build_call_args(ctx)
    fn_call_raw = f"{qualified_name} {' '.join(call_args)}"
    fn_call_expr = f"({fn_call_raw})" if ' ' in fn_call_raw else fn_call_raw
    induct_clause = _build_induct_clause(ctx, qualified_name)

    acc_name = ctx.accumulators[0] if ctx.accumulators else "acc"
    source_expr = ctx.copy_source_expr or f"a[{rec_var}]!"
    start_idx = ctx.copy_start_idx or "0"

    # Find the array parameter (fixed arg with Array type)
    array_param = ""
    for p in ctx.parameters:
        if "Array" in (p.get("type", "") or "") and p["name"] in ctx.fixed_args:
            array_param = p["name"]
            break
    if not array_param:
        for cv in ctx.captured_vars:
            if "Array" in (cv.get("type", "") or ""):
                array_param = cv["name"]
                break
    if not array_param:
        array_param = "a"

    helper_name = f"{ctx.fn_name}_spec"
    helper_name = _deduplicate_name(helper_name, ctx.file_text)

    # Build parameter signature
    sig_parts = []
    for cv in ctx.captured_vars:
        sig_parts.append(f"({cv['name']} : {cv.get('type', '_')})")
    for p in ctx.parameters:
        sig_parts.append(f"({p['name']} : {p.get('type', '_')})")

    # Hypotheses: bound, subtraction precondition, size invariant, element invariant
    sig_parts.append(f"(h{rec_var} : {rec_var} ≤ {bound})")

    # Add 1 ≤ i hypothesis if start_idx suggests subtraction
    if start_idx != "0":
        sig_parts.append(f"(h1 : {start_idx} ≤ {rec_var})")
        sig_parts.append(f"(hacc_size : {acc_name}.size = {rec_var} - {start_idx})")
    else:
        sig_parts.append(f"(hacc_size : {acc_name}.size = {rec_var})")

    # Element invariant
    # Infer the element relationship from source_expr
    # e.g., a[i]! → acc[j]! = a[j + startIdx]!
    if start_idx != "0":
        lines.append(f"theorem {helper_name} {' '.join(sig_parts)}")
        lines.append(f"    (hacc_elems : ∀ j : Nat, j < {acc_name}.size → {acc_name}[j]! = {array_param}[j + {start_idx}]!) :")
    else:
        lines.append(f"theorem {helper_name} {' '.join(sig_parts)}")
        lines.append(f"    (hacc_elems : ∀ j : Nat, j < {acc_name}.size → {acc_name}[j]! = {array_param}[j]!) :")

    # Conclusion: final result has right size and elements
    postcond = ctx.postcond_text
    # Try to extract size and element parts from postcondition
    lines.append(f"    ({fn_call_expr}).size = {bound} - {start_idx} ∧")
    if start_idx != "0":
        lines.append(f"    ∀ j : Nat, j < ({fn_call_expr}).size → ({fn_call_expr})[j]! = {array_param}[j + {start_idx}]! := by")
    else:
        lines.append(f"    ∀ j : Nat, j < ({fn_call_expr}).size → ({fn_call_expr})[j]! = {array_param}[j]! := by")

    lines.append(f"  sorry")

    lines.append("")
    lines.extend(_gen_main_proof_sketch(ctx, helper_name, qualified_name))

    return "\n".join(lines)


def _gen_search(ctx: TemplateContext) -> str:
    """Generate template for search pattern (find first index satisfying condition).

    Helper states: if ∃ j ≥ n with condition(j), then f returns the smallest such j.
    """
    lines = []

    qualified_name = _get_qualified_name(ctx)
    rec_var = ctx.recursion_var
    bound = ctx.bound_expr
    call_args = _build_call_args(ctx)
    fn_call_raw = f"{qualified_name} {' '.join(call_args)}"
    # Parenthesized version for use in expressions where precedence matters
    fn_call_expr = f"({fn_call_raw})" if ' ' in fn_call_raw else fn_call_raw
    induct_clause = _build_induct_clause(ctx, qualified_name)

    search_cond = ctx.search_condition or f"sorry /- search condition -/"

    # Helper for word-boundary-aware replacement
    def _wb_replace(text, old, new):
        return re.sub(rf'\b{re.escape(old)}\b', new, text)

    # Find the array and element params
    array_param = ""
    other_params = []
    for p in ctx.parameters:
        if "Array" in (p.get("type", "") or "") and p["name"] in ctx.fixed_args:
            array_param = p["name"]
        elif p["name"] in ctx.fixed_args:
            other_params.append(p)

    helper_name = f"{ctx.fn_name}_spec"
    helper_name = _deduplicate_name(helper_name, ctx.file_text)

    # Build parameter signature
    sig_parts = []
    for cv in ctx.captured_vars:
        sig_parts.append(f"({cv['name']} : {cv.get('type', '_')})")
    for p in ctx.parameters:
        sig_parts.append(f"({p['name']} : {p.get('type', '_')})")

    # Existence hypothesis: ∃ j, j ≥ n ∧ j < bound ∧ condition(j)
    cond_with_j = _wb_replace(search_cond, rec_var, 'j') if rec_var in search_cond else 'sorry /- condition on j -/'
    sig_parts.append(f"(hexists : ∃ j, {rec_var} ≤ j ∧ j < {bound} ∧ {cond_with_j})")

    param_sig = " ".join(sig_parts)

    lines.append(f"-- Helper lemma for {qualified_name} (search pattern)")
    lines.append(f"-- If ∃ j ≥ {rec_var} satisfying condition, returns the smallest such j")
    lines.append(f"theorem {helper_name} {param_sig} :")
    lines.append(f"    {fn_call_expr} < {bound} ∧")

    # Replace rec_var reference in condition with fn_call_expr
    result_cond = _wb_replace(search_cond, rec_var, f"{fn_call_expr}")
    lines.append(f"    {result_cond} ∧")
    cond_with_k = _wb_replace(search_cond, rec_var, 'k') if rec_var in search_cond else 'sorry'
    lines.append(f"    ∀ k, {rec_var} ≤ k → k < {fn_call_expr} → ¬({cond_with_k}) := by")

    lines.append(f"  -- Proof sketch: {induct_clause}")
    lines.append(f"  --   case condition-true: fn returns {rec_var}, trivially satisfies bound and condition")
    lines.append(f"  --   case condition-false: recurse to {rec_var}+1, shift hexists, apply ih")
    lines.append(f"  --   case guard-false: contradicts hexists via omega")
    lines.append(f"  sorry")

    lines.append("")
    lines.append(f"-- Main proof:")
    lines.append(f"-- In the main proof section, use:")
    lines.append(f"--   simp only [{ctx.postcond_name}, {ctx.main_fn_name}]")
    lines.append(f"--   have hexists : ∃ j, 0 ≤ j ∧ j < {bound} ∧ ... := by")
    lines.append(f"--     obtain ⟨...⟩ := h_precond")
    lines.append(f"--     exact ⟨..., Nat.zero_le _, ...⟩")
    lines.append(f"--   have := {helper_name} ... 0 hexists")
    lines.append(f"--   obtain ⟨h1, h2, h3⟩ := this")
    lines.append(f"--   exact ⟨h1, h2, fun k hk => h3 k (Nat.zero_le k) hk⟩")

    return "\n".join(lines)


def _gen_guarded_ascending_generic(ctx: TemplateContext) -> str:
    """Generate template for generic guarded ascending recursion using function.induct."""
    lines = []

    qualified_name = _get_qualified_name(ctx)
    rec_var = ctx.recursion_var
    bound = ctx.bound_expr
    call_args = _build_call_args(ctx)
    fn_call_raw = f"{qualified_name} {' '.join(call_args)}"
    fn_call_expr = f"({fn_call_raw})" if ' ' in fn_call_raw else fn_call_raw
    induct_clause = _build_induct_clause(ctx, qualified_name)

    helper_name = f"{ctx.fn_name}_spec"
    helper_name = _deduplicate_name(helper_name, ctx.file_text)

    # Accumulator params
    acc_params = [p for p in ctx.parameters if p["name"] in ctx.accumulators]

    # Build parameter signature
    sig_parts = []
    for cv in ctx.captured_vars:
        sig_parts.append(f"({cv['name']} : {cv.get('type', '_')})")
    for p in ctx.parameters:
        sig_parts.append(f"({p['name']} : {p.get('type', '_')})")
    sig_parts.append(f"(h{rec_var} : {rec_var} ≤ {bound})")

    # Accumulator invariant hypothesis
    if acc_params:
        acc_names = ", ".join(p["name"] for p in acc_params)
        sig_parts.append(f"(h_inv : True /- TODO: invariant relating {acc_names} to elements processed so far -/)")

    param_sig = " ".join(sig_parts)

    # Build the lifted postcondition
    postcond_lifted = _lift_postcond_for_ascending(ctx, fn_call_expr)

    lines.append(f"-- Helper lemma for {qualified_name}")
    lines.append(f"-- Proves the postcondition holds for any starting index and accumulator state")
    lines.append(f"-- Proof sketch: {induct_clause}")
    lines.append(f"--   case guard-true ({rec_var} < {bound}): unfold, apply ih")
    lines.append(f"--   case guard-false ({rec_var} ≥ {bound}): base case, fn returns accumulator")
    lines.append(f"theorem {helper_name} {param_sig} :")
    lines.append(f"    {postcond_lifted} := by")
    lines.append(f"  sorry")

    lines.append("")
    lines.extend(_gen_main_proof_sketch(ctx, helper_name, qualified_name))

    return "\n".join(lines)


def _lift_postcond_for_ascending(ctx: TemplateContext, fn_call_expr: str) -> str:
    """Lift postcondition replacing result with fn call for ascending loops."""
    postcond = ctx.postcond_text.strip()

    # Replace 'result' with the function call
    lifted = postcond.replace("result", f"({fn_call_expr})")

    # Map main function param names to recursive function/captured var names
    # e.g., postcondition uses 'arr' but recursive fn uses 'oldArr'
    if ctx.main_fn_params and ctx.postcond_params:
        # Build mapping from postcond param names to helper param names
        # The postcond params are: (main_fn_params) (result) (h_precond)
        # We need to identify which postcond params correspond to which helper params
        main_param_names = [p["name"] for p in ctx.main_fn_params]
        helper_param_names = [cv["name"] for cv in ctx.captured_vars] + [p["name"] for p in ctx.parameters]

        # Build name->type mapping for matching
        for mp in ctx.main_fn_params:
            mp_name = mp["name"]
            mp_type = mp.get("type", "")
            # Find matching param in helper by type
            for hp_name in helper_param_names:
                if hp_name == mp_name:
                    break  # already matches
            else:
                # Try type-based matching
                for hp in (ctx.captured_vars + ctx.parameters):
                    if hp.get("type") == mp_type and hp["name"] != mp_name:
                        # Replace in the lifted postcondition
                        lifted = re.sub(rf'\b{re.escape(mp_name)}\b', hp["name"], lifted)
                        break

    return lifted


def _gen_main_proof_sketch(ctx: TemplateContext, helper_name: str, qualified_name: str) -> list:
    """Generate sketch for the main theorem proof using the helper."""
    lines = []

    # Detect initial call arguments
    initial_args = ctx.initial_call_args.get("_raw", "")

    lines.append(f"-- Main proof: apply {helper_name} at initial values")
    lines.append(f"-- Initial call: {qualified_name} {initial_args}")
    lines.append(f"-- In the main proof section, use:")
    lines.append(f"--   unfold {ctx.postcond_name} {ctx.main_fn_name}")

    if ctx.fn_location == "code_aux":
        parent_name = qualified_name.split('.')[0] if '.' in qualified_name else ""
        if parent_name and parent_name != ctx.main_fn_name:
            lines.append(f"--   simp only [{parent_name}]  -- unfold code_aux wrapper")

    lines.append(f"--   apply/exact {helper_name}")
    lines.append(f"--   · omega  -- bound hypothesis")

    if ctx.accumulators:
        lines.append(f"--   · sorry  -- initial accumulator invariant")

    return lines


def _gen_structural_nat(ctx: TemplateContext) -> str:
    """Generate template for structural Nat recursion."""
    lines = []
    qualified_name = _get_qualified_name(ctx)
    rec_var = ctx.recursion_var

    # Build parameter signature (include captured vars for let rec)
    sig_parts = []
    for cv in ctx.captured_vars:
        sig_parts.append(f"({cv['name']} : {cv.get('type', '_')})")
    for p in ctx.parameters:
        sig_parts.append(f"({p['name']} : {p.get('type', '_')})")
    param_sig = " ".join(sig_parts)

    # Build function call
    call_args = _build_call_args(ctx)
    fn_call_raw = f"{qualified_name} {' '.join(call_args)}"
    fn_call_expr = f"({fn_call_raw})" if ' ' in fn_call_raw else fn_call_raw

    postcond_lifted = ctx.postcond_text.replace("result", f"({fn_call_expr})")

    helper_name = f"{ctx.fn_name}_spec"
    helper_name = _deduplicate_name(helper_name, ctx.file_text)

    lines.append(f"-- Helper lemma for {qualified_name} (structural recursion on {rec_var})")
    lines.append(f"theorem {helper_name} {param_sig}")
    lines.append(f"    (h_pre : True /- TODO: add necessary preconditions -/) :")
    lines.append(f"    {postcond_lifted} := by")
    lines.append(f"  sorry -- TODO: induction on {rec_var} using {qualified_name}.induct or pattern matching")

    lines.append("")
    lines.extend(_gen_main_proof_sketch(ctx, helper_name, qualified_name))

    return "\n".join(lines)


def _gen_guarded_descending(ctx: TemplateContext) -> str:
    """Generate template for guarded descending recursion."""
    lines = []
    qualified_name = _get_qualified_name(ctx)
    rec_var = ctx.recursion_var

    # Build parameter signature (include captured vars for let rec)
    sig_parts = []
    for cv in ctx.captured_vars:
        sig_parts.append(f"({cv['name']} : {cv.get('type', '_')})")
    for p in ctx.parameters:
        sig_parts.append(f"({p['name']} : {p.get('type', '_')})")
    param_sig = " ".join(sig_parts)

    # Build function call
    call_args = _build_call_args(ctx)
    fn_call_raw = f"{qualified_name} {' '.join(call_args)}"
    fn_call_expr = f"({fn_call_raw})" if ' ' in fn_call_raw else fn_call_raw
    postcond_lifted = ctx.postcond_text.replace("result", f"({fn_call_expr})")

    helper_name = f"{ctx.fn_name}_spec"
    helper_name = _deduplicate_name(helper_name, ctx.file_text)

    lines.append(f"-- Helper lemma for {qualified_name} (descending recursion on {rec_var})")
    lines.append(f"private theorem {helper_name} {param_sig}")
    lines.append(f"    (h_pre : True /- TODO: preconditions -/) :")
    lines.append(f"    {postcond_lifted} := by")
    lines.append(f"  sorry -- TODO: induction on {rec_var} using {qualified_name}.induct or Nat.rec")

    lines.append("")
    lines.extend(_gen_main_proof_sketch(ctx, helper_name, qualified_name))

    return "\n".join(lines)


def _gen_structural_list(ctx: TemplateContext) -> str:
    """Generate template for structural list recursion."""
    lines = []
    qualified_name = _get_qualified_name(ctx)
    rec_var = ctx.recursion_var

    # Build parameter signature (include captured vars for let rec)
    sig_parts = []
    for cv in ctx.captured_vars:
        sig_parts.append(f"({cv['name']} : {cv.get('type', '_')})")
    for p in ctx.parameters:
        sig_parts.append(f"({p['name']} : {p.get('type', '_')})")
    param_sig = " ".join(sig_parts)

    # Build function call
    call_args = _build_call_args(ctx)
    fn_call_raw = f"{qualified_name} {' '.join(call_args)}"
    fn_call_expr = f"({fn_call_raw})" if ' ' in fn_call_raw else fn_call_raw
    postcond_lifted = ctx.postcond_text.replace("result", f"({fn_call_expr})")

    helper_name = f"{ctx.fn_name}_spec"
    helper_name = _deduplicate_name(helper_name, ctx.file_text)

    lines.append(f"-- Helper lemma for {qualified_name} (structural list recursion on {rec_var})")
    lines.append(f"private theorem {helper_name} {param_sig}")
    lines.append(f"    (h_pre : True /- TODO: preconditions -/) :")
    lines.append(f"    {postcond_lifted} := by")
    lines.append(f"  sorry -- TODO: induction on {rec_var} (nil/cons cases)")

    lines.append("")
    lines.extend(_gen_main_proof_sketch(ctx, helper_name, qualified_name))

    return "\n".join(lines)


def _gen_generic(ctx: TemplateContext) -> str:
    """Fallback template for unknown recursion patterns."""
    lines = []
    qualified_name = _get_qualified_name(ctx)

    # Build parameter signature (include captured vars for let rec)
    sig_parts = []
    for cv in ctx.captured_vars:
        sig_parts.append(f"({cv['name']} : {cv.get('type', '_')})")
    for p in ctx.parameters:
        sig_parts.append(f"({p['name']} : {p.get('type', '_')})")
    param_sig = " ".join(sig_parts)

    # Build function call
    call_args = _build_call_args(ctx)
    fn_call_raw = f"{qualified_name} {' '.join(call_args)}"
    fn_call_expr = f"({fn_call_raw})" if ' ' in fn_call_raw else fn_call_raw
    postcond_lifted = ctx.postcond_text.replace("result", f"({fn_call_expr})")

    helper_name = f"{ctx.fn_name}_spec"
    helper_name = _deduplicate_name(helper_name, ctx.file_text)

    lines.append(f"-- Helper lemma for {qualified_name} (recursion kind: {ctx.recursion_kind})")
    lines.append(f"private theorem {helper_name} {param_sig}")
    lines.append(f"    (h_pre : True /- TODO: preconditions -/) :")
    lines.append(f"    {postcond_lifted} := by")
    lines.append(f"  sorry -- TODO: determine induction scheme")

    lines.append("")
    lines.extend(_gen_main_proof_sketch(ctx, helper_name, qualified_name))

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Strategy: also generate a "pure spec" approach (Strategy C from design doc)
# ---------------------------------------------------------------------------

def _gen_pure_spec_approach(ctx: TemplateContext) -> Optional[str]:
    """
    Generate an alternative template using the equational spec approach.

    For functions that compute a value matching a foldl/foldr/count, we define
    a pure spec function and prove the recursive function equals it.

    NOTE: For fold-matching problems, Strategy A (the List.foldl/drop approach)
    is now preferred. This Strategy C is kept as a fallback.
    """
    # Detect if postcondition mentions foldl, foldr, or similar
    postcond = ctx.postcond_text
    has_foldl = "foldl" in postcond or "foldr" in postcond
    has_count = "count" in postcond.lower()

    if not (has_foldl or has_count):
        return None

    # If we already generated fold_matching as primary, skip the spec approach
    # since it's redundant (the List.foldl/drop approach is more direct)
    if ctx.problem_pattern == "fold_matching":
        return None

    lines = []
    fn_name = ctx.fn_name
    rec_var = ctx.recursion_var
    bound = ctx.bound_expr

    qualified_name = _get_qualified_name(ctx)

    # Extract the foldl expression from postcondition
    foldl_match = re.search(r'(\w+\.foldl\s*\(fun\s+\w+\s+\w+\s*=>\s*[^)]+\)\s*\d+)', postcond)
    foldl_expr = foldl_match.group(1) if foldl_match else "sorry /- foldl expression -/"

    lines.append(f"-- Strategy C: Equational specification approach")
    lines.append(f"-- Define a pure spec function and prove the loop equals it")
    lines.append(f"")

    # Detect captured vars for spec function params
    spec_params = []
    for cv in ctx.captured_vars:
        spec_params.append(cv)
    # Add recursion var
    rec_param = next((p for p in ctx.parameters if p["name"] == rec_var), None)
    if rec_param:
        spec_params.append(rec_param)

    spec_sig = _param_sig(spec_params)

    lines.append(f"-- Pure specification: what the loop computes from index {rec_var} onwards")
    lines.append(f"-- def spec_from {spec_sig} : _ :=")
    lines.append(f"--   if h : {rec_var} < {bound} then")
    lines.append(f"--     sorry /- define recursively: combine element at {rec_var} with spec_from ({rec_var}+1) -/")
    lines.append(f"--   else")
    lines.append(f"--     sorry /- base value (identity element) -/")
    lines.append(f"-- termination_by {bound} - {rec_var}")
    lines.append(f"")

    # Build the helper using function.induct
    all_params_sig = []
    for cv in ctx.captured_vars:
        all_params_sig.append(f"({cv['name']} : {cv.get('type', '_')})")
    for p in ctx.parameters:
        all_params_sig.append(f"({p['name']} : {p.get('type', '_')})")
    all_params_str = " ".join(all_params_sig)

    call_args = _build_call_args(ctx)
    call_str = " ".join(call_args)

    acc_names = [p["name"] for p in ctx.parameters if p["name"] in ctx.accumulators]
    acc_name = acc_names[0] if acc_names else "acc"

    induct_clause = _build_induct_clause(ctx, qualified_name)

    lines.append(f"-- The loop computes: acc + spec_from(i)")
    lines.append(f"-- theorem {fn_name}_eq_spec {all_params_str}")
    lines.append(f"--     (h{rec_var} : {rec_var} ≤ {bound}) :")
    lines.append(f"--     {qualified_name} {call_str} = sorry /- {acc_name} + spec_from ... {rec_var} -/ := by")
    lines.append(f"--   sorry -- {induct_clause}")
    lines.append(f"")

    lines.append(f"-- Bridge: spec_from 0 = foldl expression")
    lines.append(f"-- Use Array.foldl_toList (NOT Array.foldl_loop, which doesn't exist in Lean 4.27)")
    lines.append(f"-- theorem spec_eq_foldl ... := by sorry")
    lines.append(f"")

    lines.append(f"-- Main proof combines the two:")
    lines.append(f"-- 1. {qualified_name} {ctx.initial_call_args.get('_raw', '0 0')} = 0 + spec_from 0  (by {fn_name}_eq_spec)")
    lines.append(f"-- 2. spec_from 0 = {foldl_expr}  (by spec_eq_foldl)")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Full output generation
# ---------------------------------------------------------------------------

def generate_full_output(ctx: TemplateContext) -> str:
    """Generate the complete output for a problem."""
    lines = []
    lines.append(f"-- ============================================================")
    lines.append(f"-- Generated helper template for {ctx.problem_id}")
    lines.append(f"-- Recursive function: {ctx.fn_name} ({ctx.recursion_kind})")
    lines.append(f"-- Problem pattern: {ctx.problem_pattern}")
    lines.append(f"-- Recursion variable: {ctx.recursion_var}")
    lines.append(f"-- Bound: {ctx.bound_expr}")
    lines.append(f"-- Accumulators: {ctx.accumulators}")
    lines.append(f"-- Fixed args: {ctx.fixed_args}")
    if ctx.is_let_rec:
        lines.append(f"-- Let rec: yes, captured vars: {[v['name'] for v in ctx.captured_vars]}")
    if ctx.uses_array_push:
        lines.append(f"-- Uses Array.push: yes")
    lines.append(f"-- Induction: function.induct (not fuel-based)")
    lines.append(f"-- ============================================================")
    lines.append(f"")

    # Primary template (pattern-specific)
    pattern_label = {
        "fold_matching": "Fold-matching (loop = List.foldl over drop i)",
        "copy_build": "Copy/build (accumulator via Array.push)",
        "search": "Search (find first index satisfying condition)",
        "generic": "Generic postcondition lifting with function.induct",
    }.get(ctx.problem_pattern, "Unknown")
    lines.append(f"-- === Primary strategy: {pattern_label} ===")
    lines.append(f"")
    lines.append(generate_template(ctx))
    lines.append(f"")

    # If postcond involves foldl, also generate Strategy C (unless fold_matching already covers it)
    spec_template = _gen_pure_spec_approach(ctx)
    if spec_template:
        lines.append(f"")
        lines.append(f"-- === Alternative: Pure specification approach ===")
        lines.append(f"")
        lines.append(spec_template)

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Generate proof_aux helper lemma templates for Verina problems"
    )
    parser.add_argument(
        "--problem", type=str,
        help="Single .lean file to generate template for"
    )
    parser.add_argument(
        "--problems-dir", type=str,
        help="Directory containing verina_basic_*.lean files"
    )
    parser.add_argument(
        "--targets", type=str,
        help="Comma-separated problem numbers (e.g., 57,82,68)"
    )
    parser.add_argument(
        "--output-dir", type=str,
        help="Write templates to files in this directory"
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output analysis context as JSON (for debugging)"
    )
    args = parser.parse_args()

    if not args.problem and not args.problems_dir:
        parser.error("Either --problem or --problems-dir is required")

    # Collect files
    if args.problem:
        files = [Path(args.problem).expanduser()]
    else:
        problems_dir = Path(args.problems_dir).expanduser()
        if args.targets:
            target_nums = [t.strip() for t in args.targets.split(",")]
            files = [problems_dir / f"verina_basic_{n}.lean" for n in target_nums]
        else:
            files = sorted(problems_dir.glob("verina_basic_*.lean"))
            files = [f for f in files if "_test" not in f.stem]

    output_dir = Path(args.output_dir).expanduser() if args.output_dir else None
    if output_dir:
        output_dir.mkdir(parents=True, exist_ok=True)

    for f in files:
        if not f.exists():
            print(f"Warning: {f} does not exist", file=sys.stderr)
            continue

        ctx = build_context(f)
        if ctx is None:
            print(f"-- {f.stem}: no recursive functions found, skipping", file=sys.stderr)
            continue

        if args.json:
            import dataclasses
            print(json.dumps(dataclasses.asdict(ctx), indent=2, default=str))
            continue

        output = generate_full_output(ctx)

        if output_dir:
            out_file = output_dir / f"{f.stem}_template.lean"
            out_file.write_text(output + "\n")
            print(f"  Written: {out_file}", file=sys.stderr)
        else:
            print(output)
            print()


if __name__ == "__main__":
    main()

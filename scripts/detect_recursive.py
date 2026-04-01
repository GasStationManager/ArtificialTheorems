#!/usr/bin/env python3
"""
Detect recursive functions in Verina/Lean problem files and extract their recursion structure.

Usage:
    python3 detect_recursive.py --problems-dir ~/GS/PantographEval/problems/
    python3 detect_recursive.py --problem ~/GS/PantographEval/problems/verina_basic_56.lean
    python3 detect_recursive.py --problems-dir ~/GS/PantographEval/problems/ --summary
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Optional


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class Parameter:
    name: str
    type: Optional[str] = None

@dataclass
class RecursiveFnInfo:
    name: str
    location: str  # "code_aux", "code", "solution_aux"
    parameters: list  # list of Parameter dicts
    recursion_kind: str  # "structural_nat", "guarded_ascending", "pattern_match", "well_founded", "mutual"
    recursion_var: Optional[str] = None
    termination_measure: Optional[str] = None
    base_case_condition: Optional[str] = None
    base_case_body: Optional[str] = None
    recursive_call_pattern: Optional[str] = None
    accumulators: list = field(default_factory=list)
    fixed_args: list = field(default_factory=list)
    is_let_rec: bool = False
    parent_function: Optional[str] = None  # for let rec, the enclosing function
    raw_definition: str = ""

@dataclass
class ProblemAnalysis:
    problem_id: str
    file_path: str
    has_recursive_functions: bool
    recursive_functions: list = field(default_factory=list)
    main_function_name: Optional[str] = None
    postcondition_summary: Optional[str] = None


# ---------------------------------------------------------------------------
# Section extraction
# ---------------------------------------------------------------------------

def extract_section(text: str, section_name: str) -> str:
    """Extract content between benchmark markers for a given section."""
    pattern = rf'-- !benchmark @start {re.escape(section_name)}(?:\s+\S+)?\s*\n(.*?)-- !benchmark @end {re.escape(section_name)}'
    match = re.search(pattern, text, re.DOTALL)
    if match:
        return match.group(1).strip()
    return ""


def extract_all_sections(text: str) -> dict:
    """Extract all benchmark sections from a Lean file."""
    sections = {}
    for name in ['code_aux', 'code', 'solution_aux', 'precond', 'postcond', 'postcond_aux', 'proof_aux', 'proof']:
        sections[name] = extract_section(text, name)
    return sections


# ---------------------------------------------------------------------------
# Function definition parsing
# ---------------------------------------------------------------------------

def parse_lean_params(param_str: str) -> list[dict]:
    """Parse Lean function parameters from the signature.
    
    Handles patterns like:
      (a : Array Int) (index : Nat) (current : Int)
      {T : Type} [DecidableEq T] (a : Array T) (key : T) (i keyCount : Nat)
    """
    params = []
    # Match explicit params (x : T), implicit {x : T}, instance [C T]
    for m in re.finditer(r'[({[\[]([^)\]}>]+)[)\]}>]', param_str):
        inner = m.group(1).strip()
        # Skip if it's just a type class constraint like DecidableEq T
        if inner.startswith('[') or (not ':' in inner and not re.match(r'\w', inner)):
            continue
        if ':' in inner:
            names_part, type_part = inner.split(':', 1)
            type_str = type_part.strip()
            for name in names_part.strip().split():
                name = name.strip()
                if name and re.match(r'^[a-zA-Z_]', name):
                    params.append({"name": name, "type": type_str})
        else:
            # Implicit param without type annotation
            for name in inner.strip().split():
                if name and re.match(r'^[a-zA-Z_]', name):
                    params.append({"name": name, "type": None})
    return params


def find_toplevel_defs(code: str) -> list[dict]:
    """Find top-level function definitions (def / partial def) in a code block.
    
    Handles both styles:
      1. def f (x : T) : U := body
      2. def f : T → U → V   (equation-style with | patterns)
    """
    defs = []
    
    # Split code into individual function definitions
    # Each starts with (partial )? def at the beginning of a line (or start of string)
    def_starts = list(re.finditer(r'(?:^|\n)\s*((?:partial\s+)?def\s+(\w+))', code))
    
    for i, m in enumerate(def_starts):
        name = m.group(2)
        def_start = m.start() + (1 if code[m.start()] == '\n' else 0)
        
        # Find end of this definition (start of next def, or end of code)
        if i + 1 < len(def_starts):
            def_end = def_starts[i + 1].start()
        else:
            def_end = len(code)
        
        full_def = code[def_start:def_end].strip()
        
        # Check for := style vs equation style (| patterns after type signature)
        # Be careful: `:=` can appear in `let x := ...` inside the body
        # Only count `:=` that appears before the first `|` pattern or in the signature
        first_pipe = re.search(r'^\s*\|', full_def, re.MULTILINE)
        has_equations = bool(first_pipe)
        
        # For has_assign, only look at content before first equation pattern
        pre_eq = full_def[:first_pipe.start()] if first_pipe else full_def
        # Also need to look before 'where'
        has_assign = bool(re.search(r':=\s', pre_eq))
        has_where = bool(re.search(r'\bwhere\b', pre_eq))
        
        # Extract parameters
        # For := style: def name (params) : ret :=
        # For equation style: def name : Type1 → Type2 → ... → RetType \n  | ...
        first_line_end = full_def.find('\n')
        if first_line_end == -1:
            first_line_end = len(full_def)
        
        # Try to extract param string (everything between name and : or :=)
        after_name = full_def[full_def.index(name) + len(name):]
        
        if has_assign:
            # Standard style: extract params before :=
            before_assign = after_name[:after_name.index(':=')]
            # Split at the last : to separate params from return type
            # But be careful: (x : T) contains colons too
            param_str = before_assign.strip()
            ret_type = ""
            # Try to find return type annotation
            # Count balanced parens/brackets to find the unenclosed ':'
            depth = 0
            last_colon = -1
            for ci, ch in enumerate(param_str):
                if ch in '([{':
                    depth += 1
                elif ch in ')]}':
                    depth -= 1
                elif ch == ':' and depth == 0:
                    last_colon = ci
            if last_colon >= 0:
                ret_type = param_str[last_colon + 1:].strip()
                param_str = param_str[:last_colon].strip()
            
            body_start = full_def.index(':=') + 2
            body = full_def[body_start:].strip()
        elif has_equations:
            # Equation style: def name : T1 → T2 → ... → Ret
            #   | pat1 => body1
            #   | pat2 => body2
            # Extract type signature and use equations as body
            type_sig_end = full_def.index('|') if '|' in full_def else first_line_end
            type_sig = after_name[:type_sig_end - (full_def.index(name) + len(name))].strip()
            if type_sig.startswith(':'):
                type_sig = type_sig[1:].strip()
            param_str = ""  # params are in the type signature for equation style
            ret_type = type_sig
            body = full_def[full_def.index('|'):].strip()
            
            # For equation-style, try to extract param names from the patterns
            # e.g., | r, src, sStart, dStart, 0 => r
            # The first equation's pattern gives us the parameter names
        elif has_where:
            param_str = after_name[:after_name.index('where')].strip()
            ret_type = ""
            body = full_def[full_def.index('where'):].strip()
        else:
            param_str = after_name.strip()
            ret_type = ""
            body = ""
        
        params = parse_lean_params(param_str)
        
        # For equation-style defs, try to extract param info from patterns
        if has_equations and not params:
            params = _extract_params_from_equations(body, ret_type)
        
        defs.append({
            "name": name,
            "param_str": param_str,
            "params": params,
            "ret_type": ret_type,
            "body": body.strip(),
            "full_def": full_def,
            "is_partial": full_def.strip().startswith("partial"),
            "is_equation_style": has_equations and not has_assign,
        })
    
    return defs


def _extract_params_from_equations(body: str, type_sig: str) -> list[dict]:
    """Extract parameter names from equation-style patterns and type signature.
    
    For: | r, src, sStart, dStart, 0 => r
    With type: Array Int → Array Int → Nat → Nat → Nat → Array Int
    Returns params with names from pattern and types from signature.
    """
    params = []
    
    # Find the first equation pattern
    first_eq = re.search(r'\|\s*(.+?)\s*=>', body)
    if not first_eq:
        return params
    
    pattern = first_eq.group(1)
    # Split by commas to get parameter patterns
    pat_parts = [p.strip() for p in pattern.split(',')]
    
    # Parse type signature to get types
    # Split "Array Int → Array Int → Nat → Nat → Nat → Array Int" by →
    types = []
    if type_sig:
        # Split by → but be careful of nested types
        depth = 0
        current = ""
        for ch in type_sig:
            if ch == '(' or ch == '{' or ch == '[':
                depth += 1
                current += ch
            elif ch == ')' or ch == '}' or ch == ']':
                depth -= 1
                current += ch
            elif ch == '→' and depth == 0:
                types.append(current.strip())
                current = ""
            else:
                current += ch
        if current.strip():
            types.append(current.strip())  # Last type is the return type
    
    # Map pattern parts to types (last type is return type)
    arg_types = types[:-1] if len(types) > 1 else types
    
    for i, pat in enumerate(pat_parts):
        # Get the "real" name from pattern (e.g., "0" -> skip, "n+1" -> n, "r" -> r)
        pat = pat.strip()
        if pat in ('0', '.zero', 'Nat.zero', '[]', 'true', 'false'):
            # Base case pattern - use a generic name
            name = f"_arg{i}"
        elif '+' in pat:
            name = pat.split('+')[0].strip()
        elif '::' in pat:
            name = pat.split('::')[0].strip()
        else:
            name = pat
        
        # Clean up name
        name = name.strip()
        if not re.match(r'^[a-zA-Z_]\w*$', name):
            name = f"_arg{i}"
        
        typ = arg_types[i] if i < len(arg_types) else None
        params.append({"name": name, "type": typ})
    
    return params


def find_let_rec_defs(code: str, parent_fn_name: str = "") -> list[dict]:
    """Find let rec definitions within a code block."""
    defs = []
    # Match: let rec name (params) : rettype :=
    pattern = r'let\s+rec\s+(\w+)\s*((?:[^:=]|:[^=])*?)\s*(?::\s*([^:=]+?))?\s*:='
    
    for m in re.finditer(pattern, code, re.DOTALL):
        name = m.group(1)
        param_str = m.group(2) or ""
        ret_type = (m.group(3) or "").strip()
        
        # Get body until next let rec, next top-level construct, or balanced end
        start = m.end()
        # Rough heuristic: find the next unindented line or end
        remaining = code[start:]
        # Find end of let rec body - look for next `let rec`, `let `, unindented line, or section marker
        body_end = len(remaining)
        for end_pattern in [r'\n\s*let\s+rec\s', r'\n\s*-- !benchmark']:
            end_match = re.search(end_pattern, remaining)
            if end_match and end_match.start() < body_end:
                body_end = end_match.start()
        
        body = remaining[:body_end].strip()
        
        defs.append({
            "name": name,
            "param_str": param_str,
            "params": parse_lean_params(param_str),
            "ret_type": ret_type,
            "body": body,
            "full_def": code[m.start():start + body_end].strip(),
            "is_let_rec": True,
            "parent_fn_name": parent_fn_name,
            "is_partial": False,
        })
    
    return defs


# ---------------------------------------------------------------------------
# Recursion detection and analysis
# ---------------------------------------------------------------------------

def is_self_recursive(fn_def: dict) -> bool:
    """Check if a function calls itself in its body."""
    name = fn_def["name"]
    body = fn_def["body"]
    # Look for the function name as a word boundary in the body
    # Exclude the definition line itself
    return bool(re.search(rf'\b{re.escape(name)}\b', body))


def find_recursive_calls(fn_name: str, body: str) -> list[str]:
    """Extract all lines/contexts where the function calls itself."""
    calls = []
    for line in body.split('\n'):
        if re.search(rf'\b{re.escape(fn_name)}\b', line.strip()):
            calls.append(line.strip())
    return calls


def detect_termination_measure(full_text: str, fn_name: str) -> Optional[str]:
    """Look for termination_by clause for a function."""
    # termination_by <measure>
    # Can appear after the function definition
    pattern = rf'termination_by\s+(.+?)(?:\n|$)'
    for m in re.finditer(pattern, full_text):
        measure = m.group(1).strip()
        if measure:
            return measure
    return None


def classify_recursion(fn_def: dict, full_file_text: str) -> dict:
    """Classify the recursion pattern and extract structure."""
    name = fn_def["name"]
    body = fn_def["body"]
    params = fn_def["params"]
    param_names = [p["name"] for p in params]
    
    result = {
        "recursion_kind": "unknown",
        "recursion_var": None,
        "termination_measure": None,
        "base_case_condition": None,
        "base_case_body": None,
        "recursive_call_pattern": None,
        "accumulators": [],
        "fixed_args": [],
    }
    
    # Check for termination_by in full file
    term_measure = detect_termination_measure(full_file_text, name)
    result["termination_measure"] = term_measure
    
    # --- Pattern 1: Structural Nat recursion (pattern matching on Nat) ---
    # | 0 => ... | n+1 => ... or | .zero => ... | .succ n => ...
    # Also handles equation-style: | r, src, sStart, dStart, 0 => ... | r, src, sStart, dStart, n+1 => ...
    nat_base = re.search(r'\|\s*(?:[\w,\s]*,\s*)?(?:0|\.zero|Nat\.zero)\s*=>', body)
    nat_step = re.search(r'\|\s*(?:[\w,\s]*,\s*)?(?:(\w+)\s*\+\s*1|\.succ\s+(\w+)|Nat\.succ\s+(\w+))\s*=>', body)
    
    # Also check match-based pattern: match x with | 0 => | n + 1 =>
    if not nat_base:
        nat_base = re.search(r'match\s+\w+.*?with.*?\|\s*0\s*=>', body, re.DOTALL)
    
    if nat_base and nat_step:
        step_var = nat_step.group(1) or nat_step.group(2) or nat_step.group(3)
        # Find which parameter is being matched
        match_param = re.search(r'match\s+(\w+)', body)
        
        rec_var = None
        if match_param:
            rec_var = match_param.group(1)
        
        # For equation-style defs: | r, src, sStart, dStart, 0 =>
        # Find position of 0 in the base case pattern and get the corresponding name from step case
        if not rec_var:
            base_pat = re.search(r'\|\s*([\w,\s]+,\s*0)\s*=>', body)
            step_pat = re.search(r'\|\s*([\w,\s]+,\s*\w+\s*\+\s*1)\s*=>', body)
            if base_pat and step_pat:
                base_parts = [p.strip() for p in base_pat.group(1).split(',')]
                step_parts = [p.strip() for p in step_pat.group(1).split(',')]
                for bi, bp in enumerate(base_parts):
                    if bp.strip() in ('0', 'Nat.zero', '.zero'):
                        # The corresponding step part has the variable name
                        if bi < len(step_parts):
                            sp = step_parts[bi].strip()
                            # Extract var name from "n+1"
                            vm = re.match(r'(\w+)\s*\+\s*1', sp)
                            if vm:
                                rec_var = vm.group(1)
                            else:
                                rec_var = sp
                        elif bi < len(param_names):
                            rec_var = param_names[bi]
                        break
        
        # Try to identify from the function definition line matching pattern
        if not rec_var:
            for p in param_names:
                if p in body and re.search(rf'\b{re.escape(p)}\b', body):
                    param_info = next((pp for pp in params if pp["name"] == p), None)
                    if param_info and param_info.get("type") and "Nat" in param_info["type"]:
                        rec_var = p
                        break
        
        result["recursion_kind"] = "structural_nat"
        result["recursion_var"] = rec_var or step_var
        
        # Extract base case body
        base_match = re.search(r'\|\s*(?:[\w,\s]*,\s*)?0\s*=>\s*(.*?)(?:\n\s*\||\Z)', body, re.DOTALL)
        if base_match:
            result["base_case_body"] = base_match.group(1).strip().split('\n')[0].strip()
        result["base_case_condition"] = f"{result['recursion_var']} = 0"
        
        # Find recursive call pattern
        rec_calls = find_recursive_calls(name, body)
        if rec_calls:
            result["recursive_call_pattern"] = rec_calls[-1]  # usually the last one is the recursive case
        
        # Determine accumulators vs fixed args from the recursive call
        _classify_args(name, body, params, result)
        return result
    
    # --- Pattern 2: Guarded ascending recursion (if i < bound then ... f (i+1) ... else ...) ---
    guard_match = re.search(
        r'if\s+(?:h\s*:\s*)?(\w+)\s*<\s*(.+?)\s+then',
        body
    )
    if guard_match:
        index_var = guard_match.group(1)
        bound_expr = guard_match.group(2)
        
        # Check that the function recurses with index_var + 1
        inc_pattern = re.search(
            rf'\b{re.escape(name)}\b.*?\b{re.escape(index_var)}\s*\+\s*1\b',
            body
        )
        if not inc_pattern:
            inc_pattern = re.search(
                rf'\b{re.escape(name)}\b.*?\({re.escape(index_var)}\s*\+\s*1\)',
                body
            )
        
        if inc_pattern:
            result["recursion_kind"] = "guarded_ascending"
            result["recursion_var"] = index_var
            result["base_case_condition"] = f"¬({index_var} < {bound_expr})"
            
            # Extract else branch as base case
            else_match = re.search(r'\belse\b\s*\n?\s*(.*?)(?:\n\s*(?:termination_by|decreasing_by|$))', body, re.DOTALL)
            if else_match:
                result["base_case_body"] = else_match.group(1).strip().split('\n')[0].strip()
            
            rec_calls = find_recursive_calls(name, body)
            if rec_calls:
                result["recursive_call_pattern"] = rec_calls[0]
            
            if term_measure:
                result["termination_measure"] = term_measure
            else:
                result["termination_measure"] = f"{bound_expr} - {index_var}"
            
            _classify_args(name, body, params, result)
            return result
    
    # --- Pattern 3: Guard with = 0, ≥ bound, or > 0 (descending) ---
    # 3a: if n = 0 then base else ... f (n - 1) or f (n / k) ...
    guard_eq = re.search(r'if\s+(?:h\s*:\s*)?(\w+)\s*(?:=|==)\s*0\s+then', body)
    if guard_eq:
        var = guard_eq.group(1)
        # Check for recursive call with var - 1 or var / k
        dec_pattern = re.search(rf'\b{re.escape(name)}\b.*?\({re.escape(var)}\s*[-/]\s*\d+\)', body)
        if not dec_pattern:
            dec_pattern = re.search(rf'\b{re.escape(name)}\b.*?\b{re.escape(var)}\s*[-/]\s*\d+\b', body)
        if dec_pattern:
            result["recursion_kind"] = "guarded_descending"
            result["recursion_var"] = var
            result["base_case_condition"] = f"{var} = 0"
            rec_calls = find_recursive_calls(name, body)
            if rec_calls:
                result["recursive_call_pattern"] = rec_calls[0]
            _classify_args(name, body, params, result)
            return result
    
    # 3b: if i > 0 then ... f (i - 1) ... else base
    guard_gt = re.search(r'if\s+(?:h\s*:\s*)?(\w+)\s*>\s*0\s+then', body)
    if guard_gt:
        var = guard_gt.group(1)
        dec_pattern = re.search(rf'\b{re.escape(name)}\b.*?\b{re.escape(var)}\s*-\s*1\b', body)
        if not dec_pattern:
            dec_pattern = re.search(rf'\b{re.escape(name)}\b.*?\({re.escape(var)}\s*-\s*1\)', body)
        if dec_pattern:
            result["recursion_kind"] = "guarded_descending"
            result["recursion_var"] = var
            result["base_case_condition"] = f"{var} = 0"
            rec_calls = find_recursive_calls(name, body)
            if rec_calls:
                result["recursive_call_pattern"] = rec_calls[0]
            _classify_args(name, body, params, result)
            return result
    
    # 3c: if i ≥ bound (or i >= bound) then base else ... f ... (ascending, but guard inverted)
    guard_ge = re.search(r'if\s+(?:h\s*:\s*)?(\w+)\s*[≥]|>=\s*(\S+(?:\.\w+)*)\s+then', body)
    if guard_ge:
        index_var = guard_ge.group(1) or guard_ge.group(2)
        # This is actually ascending recursion with inverted guard
        inc_pattern = re.search(rf'\b{re.escape(name)}\b.*?\b{re.escape(index_var)}\s*\+\s*1\b', body)
        if not inc_pattern:
            inc_pattern = re.search(rf'\b{re.escape(name)}\b.*?\({re.escape(index_var)}\s*\+\s*1\)', body)
        if inc_pattern:
            result["recursion_kind"] = "guarded_ascending"
            result["recursion_var"] = index_var
            rec_calls = find_recursive_calls(name, body)
            if rec_calls:
                result["recursive_call_pattern"] = rec_calls[0]
            _classify_args(name, body, params, result)
            return result
    
    # --- Pattern 4: Match-based recursion on lists ---
    # 4a: match x with | [] => | h :: t => ... f t ...
    list_base = re.search(r'\|\s*\[\]\s*=>', body)
    list_step = re.search(r'\|\s*(\w+)\s*::\s*(\w+)\s*=>', body)
    if list_base and list_step:
        result["recursion_kind"] = "structural_list"
        tail_var = list_step.group(2)
        match_var = re.search(r'match\s+(\w+)', body)
        result["recursion_var"] = match_var.group(1) if match_var else tail_var
        result["base_case_condition"] = f"{result['recursion_var']} = []"
        rec_calls = find_recursive_calls(name, body)
        if rec_calls:
            result["recursive_call_pattern"] = rec_calls[-1]
        _classify_args(name, body, params, result)
        return result
    
    # 4b: Equation-style list pattern: | [] => | a :: b :: xs => (like minListHelper)
    eq_list_base = re.search(r'\|\s*(?:[\w,\s]*,\s*)?\[\]\s*=>', body)
    eq_list_step = re.search(r'\|\s*(?:[\w,\s]*,\s*)?(\w+)\s*::\s*(\w+)\s*::\s*(\w+)(?:\s*::\s*(\w+))?\s*=>', body)
    if not eq_list_step:
        eq_list_step = re.search(r'\|\s*(?:[\w,\s]*,\s*)?(\w+)\s*::\s*(\w+)\s*=>', body)
    if eq_list_step:
        result["recursion_kind"] = "structural_list"
        # Get the tail variable from the recursive call
        rec_calls = find_recursive_calls(name, body)
        if rec_calls:
            result["recursive_call_pattern"] = rec_calls[-1]
        # Try to find which param is the list
        for p in param_names:
            param_info = next((pp for pp in params if pp["name"] == p), None)
            if param_info and param_info.get("type") and "List" in str(param_info.get("type", "")):
                result["recursion_var"] = p
                break
        _classify_args(name, body, params, result)
        return result
    
    # --- Pattern 5: Guarded with complex condition (∧, &&) ---
    # e.g., if m < a.size ∧ n < b.size then ...
    complex_guard = re.search(r'if\s+(?:h\s*:\s*)?(\w+)\s*<\s*(\S+(?:\.\w+)*)\s*[∧&]+', body)
    if complex_guard:
        index_var = complex_guard.group(1)
        bound_expr = complex_guard.group(2)
        rec_calls = find_recursive_calls(name, body)
        if rec_calls:
            result["recursion_kind"] = "guarded_ascending"
            result["recursion_var"] = index_var
            result["termination_measure"] = term_measure
            result["recursive_call_pattern"] = rec_calls[0]
            _classify_args(name, body, params, result)
            return result
    
    # --- Pattern 6: Binary search / narrowing (lo < hi) ---
    narrow_guard = re.search(r'if\s+(?:h\s*:\s*)?(\w+)\s*<\s*(\w+)\s+then', body)
    if narrow_guard:
        lo_var = narrow_guard.group(1)
        hi_var = narrow_guard.group(2)
        # Check if both lo and hi are params
        if lo_var in param_names and hi_var in param_names:
            rec_calls = find_recursive_calls(name, body)
            if rec_calls:
                result["recursion_kind"] = "well_founded"
                result["recursion_var"] = f"{hi_var} - {lo_var}"
                result["termination_measure"] = term_measure or f"{hi_var} - {lo_var}"
                result["recursive_call_pattern"] = rec_calls[0]
                _classify_args(name, body, params, result)
                return result
    
    # --- Pattern 7: Iterator-based recursion (.next, .atEnd) ---
    if re.search(r'\.atEnd\b', body) or re.search(r'\.next\b', body):
        rec_calls = find_recursive_calls(name, body)
        if rec_calls:
            result["recursion_kind"] = "iterator"
            # Try to find the iterator param
            for p in param_names:
                param_info = next((pp for pp in params if pp["name"] == p), None)
                if param_info and param_info.get("type") and "Iterator" in str(param_info.get("type", "")):
                    result["recursion_var"] = p
                    break
            result["recursive_call_pattern"] = rec_calls[0]
            _classify_args(name, body, params, result)
            return result
    
    # --- Pattern 5: General/unknown recursion ---
    # If we detect self-calls but couldn't classify the pattern
    rec_calls = find_recursive_calls(name, body)
    if rec_calls:
        result["recursion_kind"] = "unknown"
        result["recursive_call_pattern"] = rec_calls[0]
        _classify_args(name, body, params, result)
    
    return result


def _classify_args(fn_name: str, body: str, params: list[dict], result: dict):
    """Classify parameters as accumulators (change each call) vs fixed (constant)."""
    param_names = [p["name"] for p in params]
    if not param_names:
        return
    
    # Find the recursive call and see which args change
    # Look for: fn_name arg1 arg2 arg3 ...
    # This is approximate - we look for the function call and try to extract args
    rec_call_lines = find_recursive_calls(fn_name, body)
    if not rec_call_lines:
        return
    
    # Use the first recursive call
    rec_line = rec_call_lines[0]
    
    accumulators = []
    fixed_args = []
    
    for p in param_names:
        # Skip implicit/instance params and the recursion variable
        if p == result.get("recursion_var"):
            continue
        
        # Check if the param name appears modified in the recursive call line
        # Heuristic: if the recursive call contains something other than just the param name
        # in the corresponding position, it's an accumulator
        
        # Simple heuristic: look for new_<param>, <param> + 1, modified patterns
        modified_patterns = [
            rf'\bnew_{re.escape(p)}\b',
            rf'\bnew{re.escape(p.capitalize())}\b',
            rf'\b{re.escape(p)}\s*\+\s*\d',
            rf'\b{re.escape(p)}\s*-\s*\d',
            rf'if\s+.*\bthen\s+{re.escape(p)}\s*\+',
        ]
        
        is_modified = False
        for pat in modified_patterns:
            if re.search(pat, body):
                is_modified = True
                break
        
        # Also check: does the recursive call use this param name directly?
        # If the recursive call has `fn_name ... param ...` with just param, it's likely fixed
        if is_modified:
            accumulators.append(p)
        else:
            # Check if param appears in recursive call as-is
            if re.search(rf'\b{re.escape(fn_name)}\b.*\b{re.escape(p)}\b', rec_line):
                fixed_args.append(p)
            else:
                # Param doesn't appear directly -> might be an accumulator with complex expr
                accumulators.append(p)
    
    result["accumulators"] = accumulators
    result["fixed_args"] = fixed_args


# ---------------------------------------------------------------------------
# Main analysis
# ---------------------------------------------------------------------------

def analyze_file(file_path: Path) -> ProblemAnalysis:
    """Analyze a single Lean file for recursive functions."""
    text = file_path.read_text()
    problem_id = file_path.stem  # e.g., "verina_basic_56"
    
    sections = extract_all_sections(text)
    
    all_recursive_fns = []
    
    # 1. Check code_aux for top-level recursive defs
    if sections["code_aux"]:
        for fn_def in find_toplevel_defs(sections["code_aux"]):
            if is_self_recursive(fn_def):
                info = classify_recursion(fn_def, text)
                rec_fn = RecursiveFnInfo(
                    name=fn_def["name"],
                    location="code_aux",
                    parameters=fn_def["params"],
                    raw_definition=fn_def["full_def"],
                    **info,
                )
                all_recursive_fns.append(rec_fn)
        
        # Also check for let rec in code_aux
        for fn_def in find_let_rec_defs(sections["code_aux"]):
            if is_self_recursive(fn_def):
                info = classify_recursion(fn_def, text)
                rec_fn = RecursiveFnInfo(
                    name=fn_def["name"],
                    location="code_aux",
                    parameters=fn_def["params"],
                    is_let_rec=True,
                    parent_function=fn_def.get("parent_fn_name", ""),
                    raw_definition=fn_def["full_def"],
                    **info,
                )
                all_recursive_fns.append(rec_fn)
    
    # 2. Check code for let rec definitions
    if sections["code"]:
        # Find the main function name from the file
        main_fn_match = re.search(r'def\s+(\w+)\s*.*?h_precond\b', text)
        parent_fn = main_fn_match.group(1) if main_fn_match else ""
        
        for fn_def in find_let_rec_defs(sections["code"], parent_fn):
            if is_self_recursive(fn_def):
                info = classify_recursion(fn_def, text)
                rec_fn = RecursiveFnInfo(
                    name=fn_def["name"],
                    location="code",
                    parameters=fn_def["params"],
                    is_let_rec=True,
                    parent_function=parent_fn,
                    raw_definition=fn_def["full_def"],
                    **info,
                )
                all_recursive_fns.append(rec_fn)
    
    # 3. Check solution_aux for recursive defs  
    if sections.get("solution_aux"):
        # Could be in extract_section via a different key
        pass
    # Also scan solution_aux from full text
    sol_aux = extract_section(text, "solution_aux")
    if sol_aux:
        for fn_def in find_toplevel_defs(sol_aux):
            if is_self_recursive(fn_def):
                info = classify_recursion(fn_def, text)
                rec_fn = RecursiveFnInfo(
                    name=fn_def["name"],
                    location="solution_aux",
                    parameters=fn_def["params"],
                    raw_definition=fn_def["full_def"],
                    **info,
                )
                all_recursive_fns.append(rec_fn)
    
    # Extract main function name
    main_fn_match = re.search(r'def\s+(\w+)\s*.*?h_precond\b', text)
    main_fn_name = main_fn_match.group(1) if main_fn_match else None
    
    # Extract postcondition summary
    postcond = sections.get("postcond", "")
    postcond_summary = postcond[:200] + "..." if len(postcond) > 200 else postcond
    
    return ProblemAnalysis(
        problem_id=problem_id,
        file_path=str(file_path),
        has_recursive_functions=len(all_recursive_fns) > 0,
        recursive_functions=[asdict(fn) for fn in all_recursive_fns],
        main_function_name=main_fn_name,
        postcondition_summary=postcond_summary if postcond else None,
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Detect recursive functions in Verina/Lean problem files"
    )
    parser.add_argument(
        "--problems-dir",
        type=str,
        help="Directory containing verina_basic_*.lean files",
    )
    parser.add_argument(
        "--problem",
        type=str,
        help="Single .lean file to analyze",
    )
    parser.add_argument(
        "--summary",
        action="store_true",
        help="Print a summary table instead of full JSON",
    )
    parser.add_argument(
        "--only-recursive",
        action="store_true",
        help="Only output files that contain recursive functions",
    )
    parser.add_argument(
        "--output", "-o",
        type=str,
        help="Output file (default: stdout)",
    )
    
    args = parser.parse_args()
    
    if not args.problems_dir and not args.problem:
        parser.error("Either --problems-dir or --problem is required")
    
    # Collect files to analyze
    if args.problem:
        files = [Path(args.problem).expanduser()]
    else:
        problems_dir = Path(args.problems_dir).expanduser()
        files = sorted(problems_dir.glob("verina_basic_*.lean"))
        # Exclude test files
        files = [f for f in files if "_test" not in f.stem]
    
    # Analyze each file
    analyses = []
    for f in files:
        if not f.exists():
            print(f"Warning: {f} does not exist", file=sys.stderr)
            continue
        analysis = analyze_file(f)
        if args.only_recursive and not analysis.has_recursive_functions:
            continue
        analyses.append(analysis)
    
    # Output
    if args.summary:
        print_summary(analyses)
    else:
        output = {
            "total_files": len(files),
            "files_with_recursive_functions": sum(1 for a in analyses if a.has_recursive_functions),
            "total_recursive_functions": sum(len(a.recursive_functions) for a in analyses),
            "analyses": [asdict(a) for a in analyses] if not args.only_recursive else [asdict(a) for a in analyses],
        }
        
        json_str = json.dumps(output, indent=2, default=str)
        
        if args.output:
            Path(args.output).write_text(json_str)
            print(f"Output written to {args.output}", file=sys.stderr)
        else:
            print(json_str)
    
    # Print stats to stderr
    total = len(files)
    with_rec = sum(1 for a in analyses if a.has_recursive_functions)
    total_fns = sum(len(a.recursive_functions) for a in analyses)
    
    print(f"\n--- Summary ---", file=sys.stderr)
    print(f"Total files analyzed: {total}", file=sys.stderr)
    print(f"Files with recursive functions: {with_rec}", file=sys.stderr)
    print(f"Total recursive functions found: {total_fns}", file=sys.stderr)
    
    # Breakdown by recursion kind
    kinds = {}
    for a in analyses:
        for fn in a.recursive_functions:
            kind = fn.get("recursion_kind", "unknown")
            kinds[kind] = kinds.get(kind, 0) + 1
    if kinds:
        print(f"\nRecursion kinds:", file=sys.stderr)
        for kind, count in sorted(kinds.items(), key=lambda x: -x[1]):
            print(f"  {kind}: {count}", file=sys.stderr)
    
    # Breakdown by location
    locs = {}
    for a in analyses:
        for fn in a.recursive_functions:
            loc = fn.get("location", "unknown")
            locs[loc] = locs.get(loc, 0) + 1
    if locs:
        print(f"\nLocations:", file=sys.stderr)
        for loc, count in sorted(locs.items(), key=lambda x: -x[1]):
            print(f"  {loc}: {count}", file=sys.stderr)


def print_summary(analyses: list):
    """Print a human-readable summary table."""
    print(f"{'Problem':<25} {'Recursive Fns':<40} {'Kind':<22} {'Rec Var':<15} {'Location':<12}")
    print("-" * 114)
    
    for a in analyses:
        if not a.has_recursive_functions:
            continue
        for i, fn in enumerate(a.recursive_functions):
            pid = a.problem_id if i == 0 else ""
            print(f"{pid:<25} {fn['name']:<40} {fn['recursion_kind']:<22} {fn.get('recursion_var') or '?':<15} {fn['location']:<12}")


if __name__ == "__main__":
    main()

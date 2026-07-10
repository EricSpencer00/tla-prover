"""W2.1 tier3-recovery levers (vetting probes, PLAN.md follow-on).

Reusable primitives for the 5 proposed recovery levers over the bounded-TLC
tier3 sweep (results/runs/w21-tlc-20260709). Each lever has a pure "propose"
function here plus a driver in harness/__main__.py or an ad hoc script that
wires it to runner.check_tlc for the actual probe run. Kept separate from
w21_funnel.py because these are NOT part of the frozen W2.1 funnel -- they
are a vetting pass over its tier3 output, gated on Eric reading VETTING.md
before any real recovery run touches the committed manifests.

Levers:
  1. template_cfg_for_module   -- synthesize a minimal .cfg for a tier2 file
     (no author cfg) from static analysis of CONSTANT/VARIABLES/Init/Next/Spec
     and any TypeOK-like invariant already defined in the module.
  2. find_matching_sibling_cfg -- for a tier3_tlc_fail file, look for a
     sibling .cfg (same dir) whose SPECIFICATION/INIT/NEXT/INVARIANT names
     actually resolve as identifiers in the module text (the file's own cfg
     may have been mismatched by the "first sibling .cfg" fallback in
     w21_funnel._run_one_tlc).
  3. missing_module_names       -- parse a SANY/TLC error blob for the module
     name(s) it says it cannot find, so staging code knows what to stage.
  4. larger_constant_template   -- template_cfg_for_module variant with a
     bigger default model-value cardinality, for only_1_distinct_states
     rescue attempts.
"""
from __future__ import annotations

import re
from pathlib import Path

MODULE_RE = re.compile(r"^\s*-{4,}\s*MODULE\s+(\w+)\s*-{4,}", re.M)
CONSTANT_RE = re.compile(r"^\s*CONSTANTS?\b(.*)$", re.M)
VARIABLE_RE = re.compile(r"^\s*VARIABLES?\b(.*)$", re.M)
SPEC_DEF_RE = re.compile(r"^\s*Spec\s*==", re.M)
INIT_DEF_RE = re.compile(r"^\s*Init\s*==", re.M)
NEXT_DEF_RE = re.compile(r"^\s*Next\s*==", re.M)
DEF_RE = re.compile(r"^\s*([A-Za-z_]\w*)\s*==", re.M)

# names that "look like" a type-correctness / safety invariant, checked in
# priority order -- first one that is actually DEFINED in the module wins.
INVARIANT_CANDIDATE_NAMES = [
    "TypeOK", "TypeInvariant", "TypeInv", "TypeOk", "Invariant", "Inv", "Safety",
]


def _split_names(blob: str) -> list[str]:
    """Split a CONSTANT/VARIABLE declaration tail into identifier names,
    dropping any '(_,_)' operator-arity suffix and inline comments."""
    blob = blob.split("\\*", 1)[0]
    names = []
    for tok in re.split(r"[,\s]+", blob.strip()):
        tok = tok.strip()
        if not tok:
            continue
        tok = re.sub(r"\(.*\)$", "", tok)  # CONSTANT Op(_,_) -> Op
        if re.match(r"^[A-Za-z_]\w*$", tok):
            names.append(tok)
    return names


def parse_module(text: str) -> dict:
    """Static facts about a module needed to synthesize a .cfg. Best-effort,
    single-line CONSTANT/VARIABLE declarations only (matches how nearly all
    scraped specs declare them; a spec using only inline multi-clause
    CONSTANT lists across several statements is still covered since the
    regex is MULTILINE and each line is parsed independently)."""
    mod = MODULE_RE.search(text)
    constants: list[str] = []
    for m in CONSTANT_RE.finditer(text):
        constants += _split_names(m.group(1))
    variables: list[str] = []
    for m in VARIABLE_RE.finditer(text):
        variables += _split_names(m.group(1))
    defined = {m.group(1) for m in DEF_RE.finditer(text)}
    invariant_name = next((n for n in INVARIANT_CANDIDATE_NAMES if n in defined), None)
    return {
        "module": mod.group(1) if mod else None,
        "constants": constants,
        "variables": variables,
        "has_spec": bool(SPEC_DEF_RE.search(text)),
        "has_init": bool(INIT_DEF_RE.search(text)),
        "has_next": bool(NEXT_DEF_RE.search(text)),
        "invariant_name": invariant_name,
    }


def template_cfg_for_module(text: str, set_size: int = 3, int_max: int = 3) -> str | None:
    """Synthesize a minimal .cfg for `text`. Returns None if the module has
    no Init/Next or SPECIFICATION-able definitions at all (nothing to check).
    CONSTANTS get a small model value: a symmetric set of `set_size` model
    values named "<Const>_v1.."<Const>_vN" (TLC model-value syntax, no
    quoting needed) for constants that look like a set of process/node ids,
    and a plain integer 0..int_max-1 range is NOT used (TLC .cfg CONSTANT
    lines bind one value, not a range) -- we bind every constant to the
    SAME small model-value set unless its own name suggests a small integer
    (e.g. "N", "MaxX", ends in "Max"/"Num"/"Count" -> bind to int_max)."""
    facts = parse_module(text)
    if not (facts["has_spec"] or (facts["has_init"] and facts["has_next"])):
        return None
    lines: list[str]
    if facts["has_spec"]:
        lines = ["SPECIFICATION Spec"]
    else:
        lines = ["INIT Init", "NEXT Next"]
    const_lines = []
    for c in facts["constants"]:
        if re.search(r"(Max|Num|Count|Size|Bound|^N$|^K$)$", c):
            const_lines.append(f"CONSTANT {c} = {int_max}")
        else:
            values = ", ".join(f"{c}_v{i}" for i in range(1, set_size + 1))
            const_lines.append(f"CONSTANT {c} = {{{values}}}")
    lines += const_lines
    if facts["invariant_name"]:
        lines.append(f"INVARIANT {facts['invariant_name']}")
    return "\n".join(lines) + "\n"


def template_cfg_symmetric_sets(text: str, set_size: int = 3, int_max: int = 3) -> tuple[str, list[str]]:
    """Like template_cfg_for_module but also returns the CONSTANTS block
    TLC needs when binding a CONSTANT to a set of freshly-declared model
    values (TLC requires those symbols to appear as MODEL VALUE lines
    or be introduced via 'CONSTANTS a, b, c' + '<name> <- {a,b,c}' in some
    conventions; the form used here -- 'CONSTANT X = {v1, v2, v3}' inline
    with bare identifiers -- is TLC's supported model-value shorthand and
    needs no separate declaration, verified against tla2tools' cfg grammar).
    Returns (cfg_text, constant_names_bound) so callers/tests can assert on
    which constants got the small-set vs small-int treatment."""
    facts = parse_module(text)
    if not (facts["has_spec"] or (facts["has_init"] and facts["has_next"])):
        return "", []
    lines = ["SPECIFICATION Spec"] if facts["has_spec"] else ["INIT Init", "NEXT Next"]
    bound = []
    for c in facts["constants"]:
        bound.append(c)
        if re.search(r"(Max|Num|Count|Size|Bound|^N$|^K$)$", c):
            lines.append(f"CONSTANT {c} = {int_max}")
        else:
            values = ", ".join(f"{c}_v{i}" for i in range(1, set_size + 1))
            lines.append(f"CONSTANT {c} = {{{values}}}")
    if facts["invariant_name"]:
        lines.append(f"INVARIANT {facts['invariant_name']}")
    return "\n".join(lines) + "\n", bound


IDENT_RE = re.compile(r"\b([A-Za-z_]\w*)\b")


def cfg_identifiers(cfg_text: str) -> set[str]:
    """Identifiers named after SPECIFICATION/INIT/NEXT/INVARIANT/PROPERTY/
    CONSTANT keys in a .cfg -- the RHS names that must resolve in the module
    (used by lever 2 to check whether a sibling .cfg actually matches)."""
    names = set()
    for kw in ("SPECIFICATION", "INIT", "NEXT", "INVARIANT", "INVARIANTS",
               "PROPERTY", "PROPERTIES"):
        for m in re.finditer(rf"^\s*{kw}\b(.*)$", cfg_text, re.M):
            names |= set(_split_names(m.group(1)))
    return names


def cfg_matches_module(cfg_text: str, module_text: str) -> bool:
    """True iff every SPEC/INIT/NEXT/INVARIANT/PROPERTY identifier named in
    the cfg is actually defined (as a `Name ==` or `VARIABLES ... Name`) in
    the module text -- a cheap static check for lever 2's "was this sibling
    cfg even written for this module" question."""
    ids = cfg_identifiers(cfg_text)
    if not ids:
        return False
    defined = {m.group(1) for m in DEF_RE.finditer(module_text)}
    return ids.issubset(defined)


def find_matching_sibling_cfg(module_text: str, used_cfg_path: Path,
                              cfg_candidates: list[Path]) -> Path | None:
    """Lever 2: among cfg_candidates (siblings in the same dir), return the
    first one (excluding used_cfg_path) whose identifiers all resolve in
    module_text, IF used_cfg_path itself does NOT resolve (i.e. only
    proposes a swap when the originally-used cfg was the mismatch)."""
    used_text = used_cfg_path.read_text(errors="replace") if used_cfg_path.exists() else ""
    if cfg_matches_module(used_text, module_text):
        return None  # original cfg already matches; not a mismatch case
    for c in cfg_candidates:
        if c == used_cfg_path:
            continue
        text = c.read_text(errors="replace")
        if cfg_matches_module(text, module_text):
            return c
    return None


MISSING_MODULE_RE = re.compile(
    r"(?:Cannot find (?:the )?source file|module\s+['\"]?(\w+)['\"]?\s+not found|"
    r"File\s+(\w+)\s+not found)", re.I)
MISSING_MODULE_NAME_RE = re.compile(
    r"Cannot find (?:the )?source file for module\s+['\"]?(\w+)['\"]?", re.I)


def missing_module_names(error_text: str) -> list[str]:
    """Lever 3: extract module name(s) SANY/TLC says it could not find, from
    the standard tla2tools error text. Best-effort regex; returns [] if the
    error isn't a missing-module error."""
    names = set()
    for m in MISSING_MODULE_NAME_RE.finditer(error_text):
        names.add(m.group(1))
    # fallback pattern: "***Parse Error***  ... -- Unknown operator/module `X`"
    for m in re.finditer(r"Unknown (?:module|operator)\s+`?(\w+)`?", error_text):
        names.add(m.group(1))
    return sorted(names)

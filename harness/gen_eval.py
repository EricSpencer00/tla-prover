"""E2.c Gate-2 baseline eval (PLAN Amendment 12).

Two framings over the frozen 30-spec holdout (corpus/holdout_30.json):
  A -- NL->spec generation: FormaLLM description -> model emits a TLA+ module,
       scored by the Amendment-1/3 population criterion (+ Rule 9 semaudit).
  B -- repair-from-standardized-corruption: one deterministic mutation per spec,
       model repairs it, same criterion.

This module holds the deterministic pieces (cfg-signature parse, prompt build,
response parse, pass@k). Model calls reuse harness.repair's Model classes;
scoring reuses harness.runner's oracle machinery.
"""
import random
import re

from .mutation import MUTATIONS

# TLC .cfg section keywords (subset we care about for the required signature).
_CFG_KEYWORDS = {
    "CONSTANT", "CONSTANTS", "SPECIFICATION", "INIT", "NEXT",
    "INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES",
    "CONSTRAINT", "ACTION_CONSTRAINT", "SYMMETRY", "VIEW", "ALIAS",
    "CHECK_DEADLOCK", "POSTCONDITION",
}


def required_signature(cfg_text):
    """Parse a TLC .cfg into the identifiers a generated module must define:
    constants (names), specification (temporal formula name or None), init/next
    (names or None), invariants (list), properties (list). This is what the
    generation prompt tells the model to define, so the reference cfg can score
    its output."""
    sig = {"constants": [], "specification": None, "init": None, "next": None,
           "invariants": [], "properties": []}
    section = None
    for raw in cfg_text.splitlines():
        line = raw.split("\\*", 1)[0].strip()  # strip cfg comments
        if not line:
            continue
        head = line.split()[0]
        if head in _CFG_KEYWORDS:
            section = head
            rest = line[len(head):].strip()
            body = rest
        else:
            body = line
        if not body:
            continue
        if section in ("CONSTANT", "CONSTANTS"):
            # entries "Name = value" or "Name <- op"; take the left identifier
            name = re.split(r"<-|=", body, maxsplit=1)[0].strip()
            if name:
                sig["constants"].append(name)
        elif section == "SPECIFICATION":
            sig["specification"] = body.split()[0]
        elif section == "INIT":
            sig["init"] = body.split()[0]
        elif section == "NEXT":
            sig["next"] = body.split()[0]
        elif section in ("INVARIANT", "INVARIANTS"):
            sig["invariants"].extend(body.split())
        elif section in ("PROPERTY", "PROPERTIES"):
            sig["properties"].extend(body.split())
    return sig


_MODULE_RE = re.compile(r"^-{4,}\s*MODULE\b.*?^={4,}", re.S | re.M)


def extract_module(response):
    """Pull the first `---- MODULE ... ====` block out of a model response,
    tolerating markdown fences and surrounding prose. Returns the module text
    (fences stripped) or None if no complete module is present."""
    m = _MODULE_RE.search(response)
    return m.group(0).strip() if m else None


class NoCandidateMutation(Exception):
    """Raised by corrupt() when spec_text has no site where any MUTATIONS
    operator regex matches -- there is nothing to corrupt, so returning the
    text unchanged would silently make the repair task empty (forbidden by
    the E2.c handoff). Callers must catch this and exclude the spec from the
    Framing-B (repair) sample rather than treat it as a corrupted spec."""
    pass


def corrupt(spec_text, seed):
    """Option-B corruption: apply exactly ONE deterministic seeded mutation
    swap (reusing harness.mutation.MUTATIONS, the same SpecGen-style
    whole-module operator-swap regexes used by the mutation kill-rate tool)
    to spec_text, and return (corrupted_text, mutation_record).

    Determinism / seed convention: `seed` is an int chosen entirely by the
    CALLER (the orchestration step derives it from spec number + the frozen
    holdout hash -- this function does not know or care about that scheme).
    Given the same (spec_text, seed) this function always returns the same
    corrupted output.

    Site selection: for each MUTATIONS operator (in the fixed order they
    appear in mutation.MUTATIONS, which is itself fixed by that module), we
    scan spec_text for ALL non-overlapping regex matches in left-to-right
    scan order (re.finditer's natural order -- stable across Python versions/
    platforms). Each match is a candidate (operator_label, start, end,
    original_fragment, replacement_fragment). The full candidate list
    (operators concatenated in MUTATIONS order, each operator's matches in
    scan order) is then indexed with `random.Random(seed).randrange(len(...))`
    to pick exactly one candidate deterministically. Only that one match is
    replaced; every other occurrence of every operator is left untouched, so
    exactly one token in the module changes.

    Returns (corrupted_text, mutation_record) where mutation_record is a dict
    with keys: mutation (operator label from MUTATIONS), offset (character
    offset of the mutated fragment in spec_text), original (the matched
    fragment text), replacement (the fragment it was replaced with).

    If spec_text has NO site where any MUTATIONS regex matches at all, this
    raises NoCandidateMutation (documented choice: an exception, not a
    None-return, so a missed check isn't silently swallowed by a caller doing
    `if corrupted: ...`).
    """
    candidates = []
    for label, regex, replacement in MUTATIONS:
        for m in regex.finditer(spec_text):
            candidates.append((label, m.start(), m.end(), m.group(0), replacement))
    if not candidates:
        raise NoCandidateMutation(
            "no MUTATIONS operator site found in spec_text; nothing to corrupt")
    idx = random.Random(seed).randrange(len(candidates))
    label, start, end, original, replacement = candidates[idx]
    corrupted_text = spec_text[:start] + replacement + spec_text[end:]
    mutation_record = {
        "mutation": label,
        "offset": start,
        "original": original,
        "replacement": replacement,
    }
    return corrupted_text, mutation_record


# ------------------------------------------------------------- the prompts

_DESC_FIELD_ORDER = [
    "system_overview", "actors_and_components", "state_variables",
    "initial_state", "actions", "safety_properties", "liveness_properties",
    "model_bounds",
]

_DESC_FIELD_LABELS = {
    "system_overview": "System overview",
    "actors_and_components": "Actors and components",
    "state_variables": "State variables",
    "initial_state": "Initial state",
    "actions": "Actions",
    "safety_properties": "Safety properties",
    "liveness_properties": "Liveness properties",
    "model_bounds": "Model bounds",
}


def _format_description(description_json):
    """Render a FormaLLM description JSON as labeled sections, in a stable
    field order, skipping any fields absent from this particular description."""
    parts = []
    for key in _DESC_FIELD_ORDER:
        if key in description_json and description_json[key]:
            label = _DESC_FIELD_LABELS[key]
            parts.append(f"{label}: {description_json[key]}")
    # any extra fields not in the known order still get surfaced, sorted for determinism
    for key in sorted(description_json):
        if key not in _DESC_FIELD_ORDER and description_json[key]:
            parts.append(f"{key}: {description_json[key]}")
    return "\n\n".join(parts)


def _format_signature(sig):
    lines = []
    if sig["constants"]:
        lines.append("  CONSTANTS: " + ", ".join(sig["constants"]))
    if sig["specification"]:
        lines.append("  SPECIFICATION formula: " + sig["specification"])
    if sig["init"]:
        lines.append("  INIT predicate: " + sig["init"])
    if sig["next"]:
        lines.append("  NEXT action: " + sig["next"])
    if sig["invariants"]:
        lines.append("  INVARIANTS: " + ", ".join(sig["invariants"]))
    if sig["properties"]:
        lines.append("  PROPERTIES: " + ", ".join(sig["properties"]))
    return "\n".join(lines) if lines else "  (no identifiers required by the .cfg)"


GENERATION_PROMPT_TEMPLATE = """You are writing a TLA+ specification from a natural-language \
description of the system it must model. Below is the description, followed by the \
exact identifiers your module MUST define (derived from the reference TLC \
configuration that will be used to check it).

=== DESCRIPTION ===
{description}

=== REQUIRED IDENTIFIERS (from the reference .cfg) ===
{signature}

=== TASK ===
Write exactly ONE complete TLA+ module named {module_name} that defines every \
identifier listed above (the CONSTANTS as declared constants; the SPECIFICATION, \
INIT, NEXT, INVARIANTS, and PROPERTIES as operators with those exact names) and \
faithfully models the system described. Do not omit any required identifier and do \
not rename it.

Output ONLY the module, nothing else -- no prose before or after -- starting with \
`---- MODULE {module_name} ----` and ending with `====`."""


def build_generation_prompt(description_json, cfg_text, module_name):
    """Framing A prompt: FormaLLM description + required identifier signature
    (from required_signature(cfg_text)) -> instructions to emit exactly one
    TLA+ module named module_name, wrapped so extract_module can recover it."""
    return GENERATION_PROMPT_TEMPLATE.format(
        description=_format_description(description_json),
        signature=_format_signature(required_signature(cfg_text)),
        module_name=module_name)


REPAIR_PROMPT_TEMPLATE = """You are repairing a TLA+ specification so that it passes \
SANY (parser/semantic checker) and TLC model checking. Keep the change minimal and \
semantics-preserving with respect to the system being modeled; do NOT weaken or \
delete invariants/properties to force a pass.

=== SPEC ===
===BEGIN SPEC===
{broken_module}
===END SPEC===

=== FAILURE ===
{error_evidence}

Output the ENTIRE corrected module, nothing else, starting with `---- MODULE` and \
ending with `====`."""


def build_repair_prompt(broken_module, error_evidence):
    """Framing B prompt: mirrors the Stage-1 repair prompt shape in repair.py
    (spec text wrapped in BEGIN/END SPEC markers + error evidence), trimmed to
    the two pieces of text this framing has available (no fault-localized
    fragment or fixed .cfg criterion here -- those are runner/repair.py
    concerns for the full escalation loop, not this bare prompt builder)."""
    return REPAIR_PROMPT_TEMPLATE.format(
        broken_module=broken_module, error_evidence=error_evidence)


def summarize_passk(results, k):
    """results: {spec -> {"greedy": bool, "samples": [bool,...]}}.
    pass@1 counts specs whose temp-0 greedy sample passed; pass@k counts specs
    where any of the k drawn samples passed. Both spec lists are returned sorted
    numerically for a stable ledger."""
    p1 = sorted((s for s, r in results.items() if r.get("greedy")), key=int)
    pk = sorted((s for s, r in results.items() if any(r.get("samples", []))),
                key=int)
    return {"n": len(results), "pass@1": len(p1), f"pass@{k}": len(pk),
            "pass@1_specs": p1, f"pass@{k}_specs": pk}

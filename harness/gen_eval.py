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
import re

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

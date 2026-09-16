"""Semantic-preservation audit for Stage-1 model repairs (Rule 5 companion).

A model "repair" that passes TLC by *weakening what is checked* -- narrowing an
invariant, gutting Next/Init, or dropping a conjunct from a checked property -- is
a vacuous/gamed pass, not a real closure. TLC cannot catch it (the weakened spec
genuinely passes); the vacuity battery catches TRUE-equivalent / unreachable-Next
/ 1-state cases, but not a subtler narrowing. This audit surfaces exactly the
risky diffs for human sign-off: for every passing model repair it reports which
CHECKED definitions (the INVARIANT/PROPERTY/INIT/NEXT names in the .cfg, plus
their transitive dependency closure within the module) were textually changed
vs. the baseline the model started from.

It does NOT claim to decide semantic equivalence (undecidable). It classifies:
  CLEAN     -- no checked definition touched (repair was elsewhere: imports,
               operators, config-substituted constants, unrelated helpers)
  REVIEW    -- a checked definition or one of its dependencies changed; a human
               must confirm the change is semantics-preserving, not a weakening
  STRUCTURAL-- Init/Next themselves changed (behavior set redefined): always review

Usage: python3 -m harness semaudit --run-id <id> [--specs 57,92,...]
"""
import json
import re
from pathlib import Path

from .repair import baseline_text, extract_definitions, extract_candidate, resolve_cfg
from .runner import REPO, build_module_index

# names TLC actually checks, from the .cfg. INVARIANT/PROPERTY are the properties;
# INIT/NEXT/SPECIFICATION/VIEW are STRUCTURAL -- they define the behavior set or
# TLC's state abstraction, so silently rewriting them (e.g. collapsing a VIEW to
# hide a liveness counterexample -- see spec 92) is a gamed pass even though no
# named invariant changed. VIEW especially must be tracked: it is load-bearing but
# never appears in the INVARIANT/PROPERTY list. .cfg lists names either inline
# ("INVARIANT Inv") or on following indented lines ("VIEW\n  DropCommonPrefix"),
# so parsing is keyword-delimited, not per-line.
ALL_KEYS = ("SPECIFICATION", "INVARIANTS", "INVARIANT", "PROPERTIES", "PROPERTY",
            "INIT", "NEXT", "VIEW", "CONSTRAINTS", "CONSTRAINT",
            "ACTION_CONSTRAINT", "CONSTANTS", "CONSTANT", "SYMMETRY",
            "CHECK_DEADLOCK", "ALIAS", "POSTCONDITION")
STRUCTURAL_KEYS = {"INIT", "NEXT", "SPECIFICATION", "VIEW", "CONSTRAINT",
                   "CONSTRAINTS", "ACTION_CONSTRAINT"}
PROP_KEYS = {"INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES"}
KEY_LINE = re.compile(r"^\s*([A-Z_]+)\b(.*)$")
# an identifier referenced inside a definition body (over-approx: all id tokens)
IDENT = re.compile(r"\b([A-Za-z_]\w*)\b")
# TLA+ comments -- stripped before comparing bodies so comment-only edits (e.g.
# spec 141 deletes proof-sketch comments) don't read as semantic changes.
LINE_COMMENT = re.compile(r"\\\*.*")
BLOCK_COMMENT = re.compile(r"\(\*.*?\*\)", re.S)


def normalize(body: str):
    body = BLOCK_COMMENT.sub("", body)
    body = "\n".join(LINE_COMMENT.sub("", l) for l in body.splitlines())
    return re.sub(r"\s+", " ", body).strip()


def checked_names(cfg_text: str):
    inv, structural = set(), set()
    cfg_text = BLOCK_COMMENT.sub("", cfg_text or "")  # drop (* *) prose first
    # operator/CONSTANT overrides "Name <- Repl" substitute Repl for a spec
    # operator (e.g. Next <- ReductionNext): Repl is behavior-defining, so a
    # silent rewrite of it is structural. Track every RHS of a <- override.
    for m in re.finditer(r"^\s*[A-Za-z_]\w*\s*<-\s*([A-Za-z_]\w*)", cfg_text, re.M):
        structural.add(m.group(1))
    cur = None  # active PROP/STRUCTURAL section, or None
    for line in cfg_text.splitlines():
        raw = LINE_COMMENT.sub("", line)
        if not raw.strip():
            continue
        m = KEY_LINE.match(raw)
        key = m.group(1).upper() if m and m.group(1).upper() in ALL_KEYS else None
        if key:
            rest, cur = m.group(2), None
            if key in PROP_KEYS:
                cur = inv
            elif key in STRUCTURAL_KEYS:
                cur = structural
            if cur is not None:  # inline names on the keyword line
                cur.update(t for t in re.split(r"[,\s]+", rest.strip()) if t)
        elif cur is not None:  # continuation: indented names under the last keyword
            cur.update(t for t in re.split(r"[,\s]+", raw.strip()) if t)
    # CONSTANT/SYMMETRY assignments ("x = e") aren't operator names to track
    return {n for n in inv if n.isidentifier()}, \
           {n for n in structural if n.isidentifier()}


def dep_closure(names, blocks):
    """names + every definition transitively referenced from them (within module)."""
    seen, frontier = set(), set(names)
    while frontier:
        n = frontier.pop()
        if n in seen:
            continue
        seen.add(n)
        if n in blocks:
            for tok in IDENT.findall(blocks[n]):
                if tok in blocks and tok not in seen:
                    frontier.add(tok)
    return seen


def audit_spec(num, corpus, cfg_dirs, candidate_path: Path):
    orig, _ = baseline_text(num, corpus)
    orig_mod = extract_candidate(orig) or orig
    cand = candidate_path.read_text(errors="replace")
    cand_mod = extract_candidate(cand) or cand
    cfg_text, _ = resolve_cfg(num, cfg_dirs)
    inv_names, struct_names = checked_names(cfg_text)

    ob = extract_definitions(orig_mod)
    cb = extract_definitions(cand_mod)
    # compare comment/whitespace-normalized bodies: a definition counts as changed
    # only if its actual formula moved, not if a comment was added/removed
    changed = {n for n in set(ob) | set(cb)
               if normalize(ob.get(n, "")) != normalize(cb.get(n, ""))}

    inv_closure = dep_closure(inv_names, ob) | dep_closure(inv_names, cb)
    struct_closure = dep_closure(struct_names, ob) | dep_closure(struct_names, cb)

    touched_checked = sorted(changed & inv_closure)
    touched_struct = sorted(changed & struct_closure)
    if touched_struct:
        verdict = "STRUCTURAL"
    elif touched_checked:
        verdict = "REVIEW"
    else:
        verdict = "CLEAN"
    return {
        "spec": num, "verdict": verdict,
        "checked_names": sorted(inv_names), "structural_names": sorted(struct_names),
        "touched_checked_defs": touched_checked,
        "touched_structural_defs": touched_struct,
        "total_defs_changed": sorted(changed),
    }


def run_semaudit(corpus: Path, run_id: str, specs=None):
    rundir = REPO / "results" / "runs" / run_id
    rows = [json.loads(l) for l in (rundir / "rows.jsonl").read_text().splitlines() if l]
    # for each spec, the FIRST passing model attempt (baseline passes need no audit)
    winners = {}
    for r in rows:
        if r["verdict"] == "pass" and r["method"] != "repair-baseline":
            winners.setdefault(r["spec"], r)
    num2mod, _ = build_module_index(corpus)
    cfg_dirs = [("override", REPO / "corpus" / "configs" / "overrides"),
                ("original", corpus / "cfg"),
                ("draft", REPO / "corpus" / "configs" / "drafts")]
    out = []
    for num, r in sorted(winners.items(), key=lambda x: int(x[0])):
        if specs and num not in specs:
            continue
        cand = rundir / "candidates" / f"{num}-{r['method']}-{r['attempt']}.tla"
        a = audit_spec(num, corpus, cfg_dirs, cand)
        a["won_via"] = r["method"]
        out.append(a)
    (rundir / "semaudit.json").write_text(json.dumps(out, indent=2))
    print(f"=== semantic audit: {run_id} ({len(out)} model repairs) ===")
    for a in out:
        print(f"  spec {a['spec']:>3} [{a['verdict']:>10}] via {a['won_via']:<16} "
              f"checked={a['checked_names']} "
              f"touched={a['touched_checked_defs'] or a['touched_structural_defs'] or '-'}")
    n_clean = sum(1 for a in out if a["verdict"] == "CLEAN")
    print(f"\n  CLEAN {n_clean} | REVIEW/STRUCTURAL {len(out) - n_clean} "
          f"(-> semaudit.json; human confirms non-weakening)")
    return out

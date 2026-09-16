"""Mutation-operator RECALL gate (PLAN.md:480 -- the known weak gate).

The deployed battery (mutation.MUTATIONS) is four whole-module regex swaps. Two
measurements say it under-reports spec strength rather than measuring it:

  - the 2026-07-21 no_kill spot-audit
    (results/analysis/w4_nokill_spot_audit_2026-07-21.md): 10 of 12 sampled
    no_kill rows had a REAL invariant that a guard-removal mutant would violate.
    The battery never generates that mutant. Follow-up 1 of that audit is this
    module.
  - the W4 Opus waves: 40 of 100 cells returned no_site at all, and two shards
    reverse-engineered the battery's regex quirks to manufacture catches.

Both are RECALL failures of the battery. A low-recall battery makes every
no_kill / no_site verdict in a corpus ledger unreadable: it cannot be told apart
from a weak spec, which is exactly what the mutation gate exists to detect.

Method. A second REFERENCE_PROBES set corrupts the spec the way the audit says
matters, and does it LOCALLY -- one mutant per site, not one per module, which
is what lets it use operators (guard removal, comparison relaxation) that
whole-file regex could not apply safely (see the DROPPED note in mutation.py).
Both sets run through mutation.run_mutants_on_module, so a "kill" means the same
thing for both. Per spec:

  probe_safety_kills > 0, battery_safety_kills > 0   -> covered
  probe_safety_kills > 0, battery_safety_kills == 0  -> recall_miss
  probe_safety_kills == 0                            -> no_evidence (excluded)

operator_recall = covered / (covered + recall_miss). The gate FAILS below
MIN_RECALL, and names the probe operators that killed on the missed specs --
those are the operators the battery must add.

BOUND, stated plainly: this is an UPPER bound on recall. The probes never touch
a cfg-checked definition, but the deployed battery rewrites the whole module,
so it can score a "kill" by corrupting the invariant itself -- a covered verdict
earned that way is not real coverage. Tightening that needs per-occurrence
attribution the whole-module battery cannot give.

Run: python3 -m harness mutation-recall <survivors.jsonl> [--limit N]
"""
import argparse
import json
import random
import re
import sys
import tempfile
from collections import Counter
from pathlib import Path

from .mutation import run_mutants_on_module

# Recall floor. Under one half, a no_kill verdict is more likely a battery
# artifact than a spec defect, so mutation_evidence in the ledger stops carrying
# information about the spec. Not a quality target -- a readability floor.
MIN_RECALL = 0.5

# Probe sites per operator per module. The probes are localized, so a large
# module has tens of sites; each site costs one SANY + one TLC run. Sites are
# sampled at a stride so the probe is not confined to the top of the file.
MAX_SITES_PER_OPERATOR = 6

# Default sample size for the gate. Matches the 2026-07-21 audit's sample.
DEFAULT_LIMIT = 12

_WORKROOT = Path("/tmp/prove-tla-mutation-recall")


def comment_mask(text: str) -> list:
    """True at every character position inside a TLA+ comment (`\\*` to end of
    line, or a `(* ... *)` block, which nests). Probes skip these positions --
    mutating a comment produces a mutant that is textually different and
    semantically identical, which would count as a survived probe and deflate
    recall."""
    mask = [False] * len(text)
    i, depth = 0, 0
    while i < len(text):
        if depth == 0 and text.startswith("\\*", i):
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            for k in range(i, j):
                mask[k] = True
            i = j
            continue
        if text.startswith("(*", i):
            depth += 1
            mask[i] = mask[i + 1] = True
            i += 2
            continue
        if depth > 0 and text.startswith("*)", i):
            depth -= 1
            mask[i] = mask[i + 1] = True
            i += 2
            continue
        if depth > 0:
            mask[i] = True
        i += 1
    return mask


_CFG_CHECKED_RE = re.compile(r"^[ \t]*(?:INVARIANTS?|PROPERTIES|PROPERTY)\b(.*)$", re.M)
_IDENT_RE = re.compile(r"[A-Za-z_]\w*")
_TOP_DEF_RE = re.compile(r"^(?P<name>[A-Za-z_]\w*)(?:\([^)]*\))?[ \t]*==", re.M)


def checked_names(cfg_text: str) -> set:
    """The definitions the cfg checks (INVARIANT / PROPERTY)."""
    names = set()
    for m in _CFG_CHECKED_RE.finditer(cfg_text or ""):
        names.update(_IDENT_RE.findall(m.group(1)))
    return names


def protect_checked(mask, text: str, names) -> list:
    """Extend `mask` over the body of every checked definition. Probes must not
    touch the invariant itself: corrupting the property is a violation by
    construction, not evidence that the spec catches a corruption. The deployed
    battery has no such guard (it rewrites the whole module), which is one more
    reason its kill counts and the probes' are not directly comparable -- only
    the per-spec covered/miss verdict is."""
    if not names:
        return mask
    defs = list(_TOP_DEF_RE.finditer(text))
    for i, m in enumerate(defs):
        if m.group("name") not in names:
            continue
        end = defs[i + 1].start() if i + 1 < len(defs) else len(text)
        for k in range(m.start(), end):
            mask[k] = True
    return mask


def _stride_sample(items, cap=MAX_SITES_PER_OPERATOR):
    """Deterministic even spread over the sites, keeping order."""
    if len(items) <= cap:
        return list(items)
    step = len(items) / cap
    return [items[int(i * step)] for i in range(cap)]


def _replace_span(text: str, start: int, end: int, repl: str) -> str:
    return text[:start] + repl + text[end:]


def probe_guard_relax(text: str, mask) -> list:
    """The audit's exact ask: remove one guard conjunct. `/\\ <expr>` becomes
    `/\\ TRUE`, which keeps the conjunct list well-formed (deleting the line
    breaks the alignment and only produces a SANY failure). Removing a guard
    widens the reachable states, which is what a real safety invariant catches.

    A conjunct whose expression continues on a following, more-indented line is
    skipped: replacing only its first line strands the continuation."""
    out, lines, pos = [], text.splitlines(keepends=True), 0
    starts = []
    for line in lines:
        starts.append(pos)
        pos += len(line)
    for n, line in enumerate(lines):
        body = line.lstrip()
        if not body.startswith("/\\ "):
            continue
        indent = len(line) - len(body)
        if mask[starts[n] + indent]:
            continue
        expr = body[3:].strip()
        if not expr or expr == "TRUE":
            continue
        nxt = next((l for l in lines[n + 1:] if l.strip()), "")
        if nxt and (len(nxt) - len(nxt.lstrip())) > indent:
            continue    # multi-line conjunct
        head = starts[n] + indent + 3
        out.append((head, starts[n] + len(line.rstrip("\n")), "TRUE"))
    return out


def probe_conj_to_disj(text: str, mask) -> list:
    """One `/\\` occurrence becomes `\\/`. The deployed battery does this to the
    whole module at once, which usually breaks every action; one at a time it
    makes a single conjunction permissive and stays parseable."""
    out, i = [], 0
    while True:
        i = text.find("/\\", i)
        if i < 0:
            return out
        if not mask[i]:
            out.append((i, i + 2, "\\/"))
        i += 2


def probe_cmp_relax(text: str, mask) -> list:
    """One `<` or `>` becomes `<=` / `>=` -- an off-by-one on a bound. This is
    the lt_to_le operator mutation.py had to DROP because whole-file regex
    cannot tell a comparison from `<<`, `>>`, `=>`, `->`, `~>` or `|->`. One
    site at a time, with the lookaround below and SANY as the backstop, it is
    safe again."""
    out = []
    for i, c in enumerate(text):
        if c not in "<>" or mask[i]:
            continue
        prev = text[i - 1] if i else ""
        nxt = text[i + 1] if i + 1 < len(text) else ""
        if prev in "<>=|~-" or nxt in "<>=":
            continue
        out.append((i, i + 1, c + "="))
    return out


def probe_bound_shift(text: str, mask) -> list:
    """One integer literal N becomes N+1 -- widens a capacity, a range bound or
    a modulus by one. Catches invariants that are pinned to the exact model
    constants."""
    out, i, n = [], 0, len(text)
    while i < n:
        if not text[i].isdigit():
            i += 1
            continue
        j = i
        while j < n and text[j].isdigit():
            j += 1
        prev = text[i - 1] if i else ""
        nxt = text[j] if j < n else ""
        adjacent = prev.isalnum() or prev in "_." or nxt.isalnum() or nxt in "_."
        if not adjacent and not mask[i]:
            out.append((i, j, str(int(text[i:j]) + 1)))
        i = j
    return out


# label -> site generator. Deliberately disjoint from mutation.MUTATIONS: the
# gate measures what the deployed battery does NOT reach.
REFERENCE_PROBES = [
    ("guard_relax", probe_guard_relax),
    ("conj_to_disj", probe_conj_to_disj),
    ("cmp_relax", probe_cmp_relax),
    ("bound_shift", probe_bound_shift),
]


def probe_mutants(target_text: str, protect=()) -> list:
    """[(label, mutant_text), ...] for one module. Labels are `<operator>#<i>`
    so operator_recall can be attributed back to the operator that killed.
    `protect` names the cfg-checked definitions to leave alone."""
    mask = protect_checked(comment_mask(target_text), target_text, set(protect))
    out = []
    for label, sites_for in REFERENCE_PROBES:
        sites = _stride_sample(sites_for(target_text, mask))
        if not sites:
            out.append((label, None))
            continue
        for i, (start, end, repl) in enumerate(sites):
            out.append((f"{label}#{i}", _replace_span(target_text, start, end, repl)))
    return out


def probe_operator(label: str) -> str:
    return label.split("#", 1)[0]


def run_probe_on_module(tla_path: Path, cfg_text: str, module: str, timeout: int) -> dict:
    """Reference probe set through the same driver, workdir and verdict as the
    deployed battery."""
    protect = checked_names(cfg_text)
    return run_mutants_on_module(tla_path, cfg_text, module, timeout,
                                 lambda t: probe_mutants(t, protect),
                                 workroot=_WORKROOT)


def recall_row(spec_id: str, battery: dict, probe: dict) -> dict:
    """One spec's recall verdict. `killers` names the probe operators that
    scored a safety kill -- on a recall_miss those are the operators the
    deployed battery is missing."""
    b_kills = battery.get("safety_killed") or 0
    p_kills = probe.get("safety_killed") or 0
    if p_kills == 0:
        verdict = "no_evidence"
    elif b_kills > 0:
        verdict = "covered"
    else:
        verdict = "recall_miss"
    killers = sorted({probe_operator(m["mutation"]) for m in probe.get("mutants", [])
                      if m.get("safety_killed")})
    return {
        "spec": spec_id,
        "verdict": verdict,
        "battery_attempted": battery.get("attempted"),
        "battery_safety_killed": b_kills,
        "probe_attempted": probe.get("attempted"),
        "probe_safety_killed": p_kills,
        "probe_killers": killers,
    }


def summarize_recall(rows, min_recall=MIN_RECALL) -> dict:
    """Aggregate per-spec verdicts into the gate report. Recall is defined only
    over specs whose probes proved a catch is possible; specs with no probe
    evidence are reported but excluded, the same way an inapplicable mutant is
    excluded from `attempted`."""
    counts = Counter(r["verdict"] for r in rows)
    covered, miss = counts["covered"], counts["recall_miss"]
    denom = covered + miss
    recall = round(covered / denom, 2) if denom else None
    missed_ops = Counter()
    for r in rows:
        if r["verdict"] == "recall_miss":
            missed_ops.update(r["probe_killers"])

    failures = []
    if not rows:
        failures.append("no specs scored -- the gate has no input")
    elif denom == 0:
        failures.append(f"no spec produced probe evidence ({counts['no_evidence']} "
                        f"no_evidence of {len(rows)}) -- the gate has no power, so it "
                        f"cannot license any reading of mutation_evidence")
    elif recall < min_recall:
        failures.append(f"operator recall {covered}/{denom} = {recall:.0%} < "
                        f"{min_recall:.0%} -- the battery misses corruptions these "
                        f"invariants demonstrably catch, so no_kill/no_site in the "
                        f"ledger cannot be read as spec weakness. Missing operators: "
                        f"{dict(missed_ops) or '(none attributed)'}")

    return {
        "specs": len(rows),
        "covered": covered,
        "recall_miss": miss,
        "no_evidence": counts["no_evidence"],
        "operator_recall": recall,
        "missing_operators": dict(missed_ops),
        "min_recall": min_recall,
        "rows": rows,
        "failures": failures,
        "ok": not failures,
    }


def load_survivors(paths) -> list:
    """Survivor ledger rows carrying spec_text + cfg_text + module (the schema
    w2_loop writes)."""
    rows = []
    for p in paths:
        for line in Path(p).read_text().splitlines():
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            if r.get("spec_text") and r.get("cfg_text") and r.get("module"):
                rows.append(r)
    return rows


def sample_rows(rows, limit, seed=0) -> list:
    """Reproducible sample: seeded shuffle, then take `limit`, then restore
    ledger order so two runs of the gate on the same ledger score the same
    specs in the same order."""
    if limit is None or len(rows) <= limit:
        return rows
    idx = list(range(len(rows)))
    random.Random(seed).shuffle(idx)
    return [rows[i] for i in sorted(idx[:limit])]


def score_survivor(row: dict, timeout: int) -> dict:
    """Re-run both sets on one ledgered survivor and return its recall row."""
    from .mutation import run_mutation_on_module
    mod = row["module"]
    spec_id = row.get("seed_key") or row.get("cell") or mod
    with tempfile.TemporaryDirectory(prefix="mutrecall-") as d:
        tla_path = Path(d) / f"{mod}.tla"
        tla_path.write_text(row["spec_text"])
        (Path(d) / f"{mod}.cfg").write_text(row["cfg_text"])
        battery = run_mutation_on_module(tla_path, row["cfg_text"], mod, timeout)
        probe = run_probe_on_module(tla_path, row["cfg_text"], mod, timeout)
    out = recall_row(spec_id, battery, probe)
    out["ledger_mutation_evidence"] = row.get("mutation_evidence")
    return out


def main(ledgers, limit=DEFAULT_LIMIT, min_recall=MIN_RECALL, timeout=60, seed=0,
         out_path=None) -> int:
    survivors = sample_rows(load_survivors(ledgers), limit, seed)
    rows = [score_survivor(r, timeout) for r in survivors]
    rep = summarize_recall(rows, min_recall)

    print(f"\n== mutation-recall {', '.join(str(p) for p in ledgers)} ==")
    print(f"specs={rep['specs']} covered={rep['covered']} "
          f"recall_miss={rep['recall_miss']} no_evidence={rep['no_evidence']}")
    print(f"operator recall = {rep['operator_recall']} (floor {min_recall})")
    for r in rows:
        print(f"  {r['spec']}: {r['verdict']} "
              f"battery={r['battery_safety_killed']}/{r['battery_attempted']} "
              f"probe={r['probe_safety_killed']}/{r['probe_attempted']} "
              f"killers={','.join(r['probe_killers']) or '-'} "
              f"ledger={r['ledger_mutation_evidence']}")
    if out_path:
        Path(out_path).write_text(json.dumps(rep, indent=2))
    if rep["ok"]:
        print("MUTATION-RECALL: OK")
        return 0
    for f in rep["failures"]:
        print(f"MUTATION-RECALL FAIL: {f}", file=sys.stderr)
    return 1


def _cli():
    ap = argparse.ArgumentParser(prog="harness.mutation_recall")
    ap.add_argument("ledgers", nargs="+", help="w2_survivors.jsonl ledger(s)")
    ap.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    ap.add_argument("--min-recall", type=float, default=MIN_RECALL)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", default=None, help="write the report as JSON")
    a = ap.parse_args()
    raise SystemExit(main(a.ledgers, a.limit, a.min_recall, a.timeout, a.seed, a.out))


if __name__ == "__main__":
    _cli()

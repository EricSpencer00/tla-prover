"""Measure how much of the Gate-2 framing-A sany=fail mass is MECHANICALLY
repairable -- i.e. recoverable with deterministic edits that require no modeling
ability from the model at all.

Motivation (2026-07-29, gate2-w4dg-120b-A): 754/990 attempts (76.2%) died in
SANY, while only ~3% failed on genuine semantic wrongness (invariant/liveness/
deadlock). If a large share of that 76% is declaration hygiene, then pass@32
is measuring bookkeeping, not competence, and a lint pass is a cheaper lever
than more SFT data.

This probe is DIAGNOSTIC ONLY. It never touches a frozen run's rows.jsonl; it
re-parses saved candidates in a scratch dir and reports counts.

Three conservative rules, each targeting an observed failure class:
  R1 drop a CONSTANTS/VARIABLES declaration that collides with a name the
     module already gets via EXTENDS (the `CONSTANTS N, MaxNat, Nat` +
     `EXTENDS Naturals` case -- 25% of sampled sany failures)
  R2 add the EXTENDS a used-but-undefined standard operator needs
     (Cardinality -> FiniteSets, Len/Append/... -> Sequences)
  R3 drop a duplicate top-level operator definition, keeping the first

Deliberately NOT attempted: unbound identifiers (`q` used outside its
`\\E q \\in ...` scope, 20% of failures). Those need scope analysis, not a
rewrite rule, and lumping them in would inflate the "repairable" number.
"""
import json
import re
import shutil
import sys
import tempfile
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from harness.runner import check_sany  # noqa: E402

REPO = Path(__file__).resolve().parents[1]

# name -> module that defines it
BUILTIN_SOURCE = {
    "Nat": "Naturals", "Int": "Integers", "Real": "Reals",
    "Cardinality": "FiniteSets", "IsFiniteSet": "FiniteSets",
    "Seq": "Sequences", "Len": "Sequences", "Append": "Sequences",
    "Head": "Sequences", "Tail": "Sequences", "SubSeq": "Sequences",
    "SelectSeq": "Sequences",
}
DECL_RE = re.compile(r"^(\s*)(CONSTANTS?|VARIABLES?)(\s+)(.*)$")
DEF_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)\s*(?:\(.*?\))?\s*==")


def _extends(src):
    got = set()
    for line in src.splitlines():
        m = re.match(r"\s*EXTENDS\s+(.*)", line)
        if m:
            got |= {x.strip() for x in m.group(1).split(",") if x.strip()}
    return got


def r1_drop_colliding_decls(src):
    """Remove declared names that EXTENDS already provides."""
    ext = _extends(src)
    hits = []
    out = []
    for line in src.splitlines():
        m = DECL_RE.match(line)
        if not m or "==" in line:
            out.append(line)
            continue
        names = [n.strip() for n in m.group(4).split(",")]
        keep = []
        for n in names:
            base = n.split("(")[0].strip()
            if base in BUILTIN_SOURCE and BUILTIN_SOURCE[base] in ext:
                hits.append(base)
            else:
                keep.append(n)
        if not keep:
            continue  # whole declaration was redundant
        out.append(f"{m.group(1)}{m.group(2)}{m.group(3)}{', '.join(keep)}")
    return "\n".join(out), hits


def r2_add_missing_extends(src):
    """Add the EXTENDS needed by standard operators the module uses but lacks."""
    ext = _extends(src)
    defined = {m.group(1) for m in (DEF_RE.match(l) for l in src.splitlines()) if m}
    need = set()
    for name, mod in BUILTIN_SOURCE.items():
        if mod in ext or name in defined:
            continue
        if re.search(rf"\b{name}\b", src):
            need.add(mod)
    if not need:
        return src, []
    lines = src.splitlines()
    for i, line in enumerate(lines):
        if re.match(r"\s*EXTENDS\s+", line):
            lines[i] = line.rstrip() + ", " + ", ".join(sorted(need))
            return "\n".join(lines), sorted(need)
    # no EXTENDS line at all: insert after the module header
    for i, line in enumerate(lines):
        if re.match(r"\s*-{4,}\s*MODULE", line):
            lines.insert(i + 1, "EXTENDS " + ", ".join(sorted(need)))
            return "\n".join(lines), sorted(need)
    return src, []


def r3_drop_duplicate_defs(src):
    """Keep the first definition of each top-level operator, drop later ones."""
    lines = src.splitlines()
    seen = set()
    out = []
    dropped = []
    i = 0
    while i < len(lines):
        m = DEF_RE.match(lines[i])
        if m and m.group(1) in seen:
            dropped.append(m.group(1))
            i += 1
            while i < len(lines):
                nxt = lines[i]
                if DEF_RE.match(nxt) or re.match(r"\s*(-{4,}|={4,}|THEOREM|VARIABLE|CONSTANT|EXTENDS)", nxt):
                    break
                i += 1
            continue
        if m:
            seen.add(m.group(1))
        out.append(lines[i])
        i += 1
    return "\n".join(out), dropped


def lint(src):
    fixes = {}
    src, h = r1_drop_colliding_decls(src)
    if h:
        fixes["R1_drop_colliding_decl"] = h
    src, h = r2_add_missing_extends(src)
    if h:
        fixes["R2_add_extends"] = h
    src, h = r3_drop_duplicate_defs(src)
    if h:
        fixes["R3_drop_dup_def"] = h
    return src, fixes


def _module_name(src, fallback):
    m = re.search(r"-{4,}\s*MODULE\s+([A-Za-z0-9_]+)", src)
    return m.group(1) if m else fallback


def probe_one(args):
    cand, timeout = args
    src = cand.read_text(errors="replace")
    fixed, fixes = lint(src)
    if not fixes:
        return {"cand": cand.name, "fixes": {}, "before": None, "after": None}
    mod = _module_name(src, cand.stem)
    res = {"cand": cand.name, "fixes": fixes}
    for tag, text in (("before", src), ("after", fixed)):
        wd = Path(tempfile.mkdtemp(prefix="lintprobe-"))
        try:
            f = wd / f"{mod}.tla"
            f.write_text(text)
            st, _out, _dt = check_sany(f, wd, timeout)
            res[tag] = st
        finally:
            shutil.rmtree(wd, ignore_errors=True)
    return res


def main():
    run = REPO / "results" / "runs" / "gate2-w4dg-120b-A"
    rows = [json.loads(l) for l in (run / "rows.jsonl").open()]
    by = defaultdict(list)
    for r in rows:
        by[r["spec"]].append(r)
    unsolved = sorted([s for s, v in by.items() if not any(x["verdict"] == "pass" for x in v)],
                      key=int)
    print(f"unsolved specs: {len(unsolved)} -> {unsolved}")

    targets = []
    for s in unsolved:
        for r in by[s]:
            if r["verdict"].startswith("fail:sany"):
                p = run / r["candidate_path"]
                if p.exists():
                    targets.append((p, 120))
    print(f"sany-failed candidates in unsolved specs: {len(targets)}")

    with ThreadPoolExecutor(max_workers=6) as pool:
        results = list(pool.map(probe_one, targets))

    touched = [r for r in results if r["fixes"]]
    recovered = [r for r in touched if r["after"] == "pass" and r["before"] != "pass"]
    print(f"\ncandidates lint touched at all : {len(touched)}/{len(targets)}")
    print(f"candidates that NOW PARSE      : {len(recovered)}")

    rule = Counter()
    for r in recovered:
        for k in r["fixes"]:
            rule[k] += 1
    for k, v in rule.most_common():
        print(f"   {v:4d}  {k}")

    spec_of = {p.name: p.name.split("-")[0] for p, _ in targets}
    newly = defaultdict(int)
    for r in recovered:
        newly[spec_of[r["cand"]]] += 1
    print(f"\nunsolved specs with >=1 now-parsing candidate: {len(newly)}/{len(unsolved)}")
    for s in sorted(newly, key=int):
        print(f"   spec {s:>3}: {newly[s]} candidates now parse")

    out = run / "lint_probe.json"
    out.write_text(json.dumps({"results": results,
                               "recovered": len(recovered),
                               "touched": len(touched),
                               "targets": len(targets),
                               "specs_with_recovery": {k: v for k, v in newly.items()}}, indent=2))
    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()

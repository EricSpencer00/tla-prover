"""W2.7 -- structural scaffolding tier-1 experiment (prompt-level, no
training).

PLAN.md Stage-2 Round 3 W2.7: decide whether the generation gap between NL
and a TLA+ spec is representational (the model has trouble mapping NL prose
onto TLA+ variable/action structure) rather than purely a capability/sampling
problem. This module builds a deterministic, regex-based structural parser
of a seed's TLA+ spec (`extract_structure`) and renders it into a compact
"STRUCTURAL SKELETON" block (`scaffold_block`) that can be appended to the NL
prompt for a "scaffold" arm, vs. an unmodified "control" arm -- both run
through the SAME real gates as W2 (harness.w2_loop.run_loop_for_seed,
unchanged), so the only variable between arms is whether the model sees the
structural skeleton.

Testbed: `build_testbed` mines the W2 reject ledgers (results/runs/w2-gen*/
w2_attempts.jsonl) for never-survived seeds whose last rejection reason is a
structural/semantic failure (sany_fail, tlc_error, tlc_fail_invariant,
tlc_fail_deadlock) -- the seeds most likely to reveal a representational gap,
as opposed to seeds that failed on cosmetic/parsing issues.

CLI:
  python3 -m harness.w27_scaffold build-testbed --run-dirs "results/runs/w2-gen*" \\
      --out results/analysis/w27_testbed.json --n 70
  python3 -m harness.w27_scaffold run --testbed results/analysis/w27_testbed.json \\
      --arm control --model openai:gpt-oss-120b --run-id w27-control
"""
from __future__ import annotations

import argparse
import glob
import hashlib
import json
import random
import re
from pathlib import Path

DEFAULT_RAW_ROOTS = [
    Path("/Users/eric/GitHub/tla-dataset-pipeline/data/raw"),
    Path("/Users/eric/GitHub/tla-dataset-pipeline/data/raw-wide-20260710"),
]

_RAW_PREFIXES = ("data/raw-wide-20260710/", "data/raw/")


def resolve_spec_path(source: str, raw_roots=DEFAULT_RAW_ROOTS) -> Path | None:
    """Resolve a ledger `source` path (e.g. "data/raw/foo/Bar.tla" or
    "data/raw-wide-20260710/foo/Bar.tla") to a real file on disk, checking
    both raw roots. Returns None if no root has the file."""
    rel = None
    for prefix in _RAW_PREFIXES:
        if source.startswith(prefix):
            rel = source[len(prefix):]
            break
    if rel is None:
        rel = source

    for root in raw_roots:
        p = root / rel
        if p.exists():
            return p
    # fall back: try stripping either prefix against either root, in case the
    # source's declared prefix doesn't match which root actually has it.
    for prefix in _RAW_PREFIXES:
        if source.startswith(prefix):
            rel2 = source[len(prefix):]
            for root in raw_roots:
                p = root / rel2
                if p.exists():
                    return p
    return None


# --------------------------------------------------------------- structure

_MODULE_RE = re.compile(r"^-{4,}\s*MODULE\s+(\w+)\s*-{4,}", re.M)
_VAR_DECL_RE = re.compile(r"^\s*VARIABLES?\s+(.+)$", re.M)
_CONST_DECL_RE = re.compile(r"^\s*CONSTANTS?\s+(.+)$", re.M)
# top-level operator definitions: `Name == ` or `Name(args) == ` at column 0
# (TLA+ convention for top-level defs).
_OP_DEF_RE = re.compile(r"^(\w+)(?:\([^)]*\))?\s*==", re.M)
_PRIMED_VAR_RE = re.compile(r"\b(\w+)'")


def _split_names(chunk: str) -> list:
    """Split a VARIABLE/CONSTANT declaration remainder into individual
    names, honoring comma-continuation across lines (the regex only grabs
    the first line, so the caller may pass in multiple joined statements)."""
    # strip trailing comment markers / backslash line continuations
    chunk = re.sub(r"\\\*.*$", "", chunk)
    names = [n.strip() for n in chunk.split(",")]
    return [n for n in names if re.match(r"^\w+$", n)]


def extract_structure(spec_text: str) -> dict:
    """Deterministic, regex-based parser of TLA+ spec text. Returns:
      module: str | None
      variables: list[str]
      constants: list[str]
      operators: list[str]              -- all top-level operator names
      actions: list[str]                -- operators whose body primes a var
      init_ops: list[str], next_ops: list[str], spec_ops: list[str]
                                          -- present-by-name subsets of operators
      primes: dict[str, list[str]]       -- action name -> sorted var names it primes
    No model calls, no file I/O.
    """
    spec_text = spec_text or ""
    mmod = _MODULE_RE.search(spec_text)
    module = mmod.group(1) if mmod else None

    variables: list = []
    for m in _VAR_DECL_RE.finditer(spec_text):
        for n in _split_names(m.group(1)):
            if n not in variables:
                variables.append(n)

    constants: list = []
    for m in _CONST_DECL_RE.finditer(spec_text):
        for n in _split_names(m.group(1)):
            if n not in constants:
                constants.append(n)

    # locate all top-level operator defs and slice out each body as the text
    # up to the next top-level def or the ==== end-of-module marker.
    op_matches = list(_OP_DEF_RE.finditer(spec_text))
    end_marker = spec_text.find("====")
    text_end = end_marker if end_marker != -1 else len(spec_text)

    operators: list = []
    primes: dict = {}
    for i, m in enumerate(op_matches):
        name = m.group(1)
        if name in ("VARIABLE", "VARIABLES", "CONSTANT", "CONSTANTS", "MODULE",
                     "EXTENDS", "LOCAL"):
            continue
        body_start = m.end()
        body_end = op_matches[i + 1].start() if i + 1 < len(op_matches) else text_end
        body = spec_text[body_start:body_end]
        if name not in operators:
            operators.append(name)
        primed = sorted({p for p in _PRIMED_VAR_RE.findall(body) if p in variables})
        if primed:
            primes[name] = primed

    actions = [op for op in operators if op in primes]
    init_ops = [op for op in operators if op == "Init"]
    next_ops = [op for op in operators if op == "Next"]
    spec_ops = [op for op in operators if op == "Spec"]

    return {
        "module": module,
        "variables": variables,
        "constants": constants,
        "operators": operators,
        "actions": actions,
        "init_ops": init_ops,
        "next_ops": next_ops,
        "spec_ops": spec_ops,
        "primes": primes,
    }


def scaffold_block(structure: dict) -> str:
    """Render a compact "STRUCTURAL SKELETON" text block suitable for
    appending to an NL prompt."""
    lines = ["STRUCTURAL SKELETON:"]
    lines.append(f"Module: {structure.get('module') or '(unknown)'}")
    variables = structure.get("variables") or []
    lines.append("Variables: " + (", ".join(variables) if variables else "(none detected)"))
    constants = structure.get("constants") or []
    lines.append("Constants: " + (", ".join(constants) if constants else "(none detected)"))
    for action in structure.get("actions") or []:
        vs = structure.get("primes", {}).get(action) or []
        vstr = ", ".join(vs) if vs else "(none detected)"
        lines.append(f"Action {action} updates: {vstr}")
    return "\n".join(lines)


# --------------------------------------------------------------- testbed

def _iter_attempt_rows(run_dirs):
    """Yield (ledger_path, row_index, row) across every w2_attempts.jsonl
    matched by run_dirs glob patterns, in sorted-path / file order (for
    determinism)."""
    ledgers = set()
    for pattern in run_dirs:
        for p in glob.glob(pattern):
            lp = Path(p) / "w2_attempts.jsonl"
            if lp.exists():
                ledgers.add(lp)
    for lp in sorted(ledgers):
        with open(lp) as f:
            for i, line in enumerate(f):
                line = line.strip()
                if not line:
                    continue
                try:
                    row = json.loads(line)
                except json.JSONDecodeError:
                    continue
                yield lp, i, row


def build_testbed(run_dirs, out_path, n: int = 70,
                   reasons=("sany_fail", "tlc_error", "tlc_fail_invariant",
                            "tlc_fail_deadlock"),
                   raw_roots=DEFAULT_RAW_ROOTS) -> dict:
    """Mine the W2 reject ledgers for a stratified testbed of never-survived
    seeds whose last rejection reason is in `reasons`. See module docstring."""
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    survived_keys = set()
    last_row_by_key = {}
    for _lp, _i, row in _iter_attempt_rows(run_dirs):
        key = row.get("seed_key")
        if key is None:
            continue
        if row.get("survived"):
            survived_keys.add(key)
        last_row_by_key[key] = row  # later ledgers/rows overwrite -> "last seen"

    candidates = []
    for key, row in last_row_by_key.items():
        if key in survived_keys:
            continue
        reason = row.get("rejection_reason")
        if reason not in reasons:
            continue
        nl = row.get("nl")
        if not nl:
            continue
        source = row.get("source")
        if not source:
            continue
        spec_path = resolve_spec_path(source, raw_roots)
        if spec_path is None:
            continue
        candidates.append({
            "source": source,
            "seed_key": key,
            "module": row.get("module"),
            "rejection_reason": reason,
            "nl": nl,
        })

    candidate_pool_size = len(candidates)

    # deterministic shared shuffle seed derived from the sorted source-path
    # pool (computed once, shared across strata).
    sorted_sources = sorted(c["source"] for c in candidates)
    seed_int = int(hashlib.sha256(json.dumps(sorted_sources).encode()).hexdigest()[:16], 16)

    # group by reason, sort each group by source for determinism, then shuffle
    # each group with an RNG derived from the shared seed (offset by reason so
    # different reasons don't produce identical orderings).
    by_reason: dict = {r: [] for r in reasons}
    for c in candidates:
        by_reason.setdefault(c["rejection_reason"], []).append(c)
    for r in by_reason:
        by_reason[r].sort(key=lambda c: c["source"])
        rng = random.Random(seed_int ^ hash(r) & 0xFFFFFFFF)
        rng.shuffle(by_reason[r])

    n_target = min(n, candidate_pool_size)

    # proportional stratification via largest remainder method
    per_reason_counts = {}
    if candidate_pool_size > 0:
        raw_shares = {}
        for r in reasons:
            pool = len(by_reason.get(r, []))
            raw_shares[r] = (pool / candidate_pool_size) * n_target if candidate_pool_size else 0.0
        floors = {r: int(raw_shares[r]) for r in reasons}
        allocated = sum(floors.values())
        remainder = n_target - allocated
        # largest-remainder order, deterministic tie-break by reason name
        remainders = sorted(reasons, key=lambda r: (-(raw_shares[r] - floors[r]), r))
        for r in remainders:
            if remainder <= 0:
                break
            # don't allocate more than the pool for that reason has
            if floors[r] < len(by_reason.get(r, [])):
                floors[r] += 1
                remainder -= 1
        # if still remainder left (pools exhausted), spill into any reason
        # with spare candidates, deterministic order.
        if remainder > 0:
            for r in sorted(reasons):
                while remainder > 0 and floors[r] < len(by_reason.get(r, [])):
                    floors[r] += 1
                    remainder -= 1
        per_reason_counts = floors
    else:
        per_reason_counts = {r: 0 for r in reasons}

    seeds = []
    for r in reasons:
        take = per_reason_counts.get(r, 0)
        seeds.extend(by_reason.get(r, [])[:take])

    derivation = (
        "Testbed mined from W2 reject ledgers matched by run-dir glob "
        f"patterns {list(run_dirs)!r}. A seed is 'never-survived' if no "
        "attempt row anywhere across the matched ledgers has survived=true "
        "for its seed_key. Candidates are deduped by seed_key (keyed by the "
        "seed's source spec path), using the LAST attempt row seen (in "
        "sorted-ledger-path/file order) as authoritative for rejection_reason/"
        f"nl/module. Filtered to candidates whose last rejection_reason is "
        f"one of {list(reasons)!r}, whose row has a non-empty nl, and whose "
        "spec file resolves to an existing file on disk (checked under both "
        "the raw and raw-wide-20260710 roots). The filtered pool "
        f"(candidate_pool_size={candidate_pool_size}) is stratified "
        f"proportionally by rejection_reason across n={n_target} slots via "
        "the largest-remainder method. Within each stratum, candidates are "
        "sorted by source path, then shuffled with random.Random(seed) where "
        "seed is derived by sha256-hashing the sorted JSON list of the full "
        "filtered candidate pool's source paths (shared across strata, "
        "computed once) XORed per-reason for stratum-distinct orderings, "
        "and the first `take` entries of each stratum's shuffled list are "
        "selected -- fully deterministic given the same ledgers on disk."
    )

    result = {
        "derivation": derivation,
        "n": n_target,
        "candidate_pool_size": candidate_pool_size,
        "reasons": list(reasons),
        "per_reason_counts": per_reason_counts,
        "seeds": seeds,
    }
    out_path.write_text(json.dumps(result, indent=2))
    return result


# --------------------------------------------------------------- run

def run_w27(model, testbed_path, run_dir, arm: str, timeout: int = 60,
            max_iters: int = 4, raw_roots=DEFAULT_RAW_ROOTS):
    """Run the W2 loop (unchanged) over a testbed for one arm (control or
    scaffold). Resumable: skips (seed_key, arm) pairs already present in
    run_dir/w27_rows.jsonl."""
    from . import w2_loop

    if arm not in ("control", "scaffold"):
        raise ValueError(f"arm must be 'control' or 'scaffold', got {arm!r}")

    run_dir = Path(run_dir)
    run_dir.mkdir(parents=True, exist_ok=True)
    testbed = json.loads(Path(testbed_path).read_text())
    seeds = testbed["seeds"]

    rows_path = run_dir / "w27_rows.jsonl"
    done = set()
    if rows_path.exists():
        for line in open(rows_path):
            line = line.strip()
            if not line:
                continue
            row = json.loads(line)
            done.add((row.get("seed_key"), row.get("arm")))

    n_survived = 0
    n_total = 0

    with open(rows_path, "a") as f:
        for i, seed in enumerate(seeds):
            seed_key = seed["seed_key"]
            if (seed_key, arm) in done:
                n_total += 1
                continue

            nl_input = seed["nl"]
            if arm == "scaffold":
                spec_path = resolve_spec_path(seed["source"], raw_roots)
                if spec_path is not None:
                    spec_text = spec_path.read_text(errors="replace")
                    nl_input = nl_input + "\n\n" + scaffold_block(extract_structure(spec_text))

            workdir = run_dir / "work" / str(i)
            result = w2_loop.run_loop_for_seed(
                model, nl_input, seed.get("module") or "Gen", workdir,
                timeout=timeout, max_iters=max_iters)

            survived = bool(result.get("survived"))
            iters = result.get("iters")
            row = {
                "seed_key": seed_key,
                "arm": arm,
                "survived": survived,
                "iters": iters,
                "rejection_reason": None if survived else result.get("rejection_reason"),
            }
            f.write(json.dumps(row) + "\n")
            f.flush()

            n_total += 1
            if survived:
                n_survived += 1
            print(f"[{n_total}/{len(seeds)}] survived={n_survived}")

    return n_survived, n_total


# --------------------------------------------------------------- CLI

def main():
    ap = argparse.ArgumentParser(prog="harness.w27_scaffold")
    sub = ap.add_subparsers(dest="cmd", required=True)

    bt = sub.add_parser("build-testbed")
    bt.add_argument("--run-dirs", action="append", required=True,
                     help="glob pattern for run dirs containing w2_attempts.jsonl; "
                          "may be given multiple times")
    bt.add_argument("--out", type=Path, required=True)
    bt.add_argument("--n", type=int, default=70)

    rn = sub.add_parser("run")
    rn.add_argument("--testbed", type=Path, required=True)
    rn.add_argument("--arm", choices=["control", "scaffold"], required=True)
    rn.add_argument("--model", required=True)
    rn.add_argument("--run-id", required=True)
    rn.add_argument("--timeout", type=int, default=60)
    rn.add_argument("--max-iters", type=int, default=4)

    a = ap.parse_args()

    if a.cmd == "build-testbed":
        result = build_testbed(a.run_dirs, a.out, n=a.n)
        print(f"testbed: n={result['n']} candidate_pool_size={result['candidate_pool_size']} "
              f"per_reason_counts={result['per_reason_counts']}")
    elif a.cmd == "run":
        from .repair import make_model
        model = make_model(a.model)
        run_dir = Path("results/runs") / a.run_id
        n_survived, n_total = run_w27(model, a.testbed, run_dir, a.arm,
                                       timeout=a.timeout, max_iters=a.max_iters)
        print(f"W2.7 {a.arm}: {n_survived}/{n_total} survived")


if __name__ == "__main__":
    main()

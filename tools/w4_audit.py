#!/usr/bin/env python3
"""W4 wave audit: effective-corpus accounting, composite stop floors, near-dup sweep.

Run from repo root after each wave:

    python3 tools/w4_audit.py

Exists so the cloud routine never has to inline the audit or read a ledger into
context: it prints a fixed-size summary and nothing else. Spec text is never
echoed -- only seed_keys.

Exit code 0 = keep going, 10 = every stop floor met (write W4_FLOOR_REACHED.md).
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from harness.corpora import (  # noqa: E402
    NEAR_DUP_THRESHOLD,
    SHINGLE_K,
    normalize_tla,
    shingle_set,
)
from harness.corpus_prep import tag_family  # noqa: E402

# ---------------------------------------------------------------------------
# STOP FLOORS -- the only numbers worth editing.
#
# The design doc (docs/designs/2026-07-17-cross-family-flywheel.md:48) says
# ">=5k rows, family-balanced". The older 4130 target subtracted ~870 pre-W4
# rows; we dropped that because it stops the run at 3% liveness. Total and
# liveness are hard gates. Family is advisory: the lattice cell -> family map is
# deterministic, so a hard family gate could be unreachable and never stop.
# ---------------------------------------------------------------------------
FLOOR_TOTAL = 5000
FLOOR_LIVENESS = 500
FAMILY_MAX_SHARE = 0.30  # advisory only

EXCLUSIONS = Path("results/analysis/w4_exclusions.json")
RUNS = Path("results/runs")


def max_shard() -> int:
    shards = [int(p.name.split("shard")[1]) for p in RUNS.glob("w4-opus-shard*")]
    if not shards:
        sys.exit("no w4-opus-shard* dirs under results/runs")
    return max(shards)


def load_effective(upto: int) -> list[dict]:
    """Effective corpus: survivors, minus exclusions, first-wins unless the key
    is a keep-last override. Mirrors the accounting in docs/RESUME_W4.md."""
    d = json.loads(EXCLUSIONS.read_text()) if EXCLUSIONS.exists() else {}
    excluded = set(d.get("excluded_seed_keys", []))
    keep_last = set(d.get("dedup_overrides", {}))

    rows: dict[str, dict] = {}
    for s in range(upto + 1):
        p = RUNS / f"w4-opus-shard{s}" / "w2_survivors.jsonl"
        if not p.exists():
            continue
        for line in p.read_text().splitlines():
            if not line.strip():
                continue
            r = json.loads(line)
            if not r.get("survived", True):
                continue
            k = r.get("seed_key")
            if k in excluded:
                continue
            if k in rows and k not in keep_last:
                continue
            r["_shard"] = s
            rows[k] = r
    return list(rows.values())


def near_dups(rows: list[dict], since_shard: int | None) -> list[tuple]:
    """Jaccard-shingle near-dup pairs.

    Incremental by default: only rows from `since_shard` onward are compared
    (against everything, and among themselves). Every earlier pair was already
    audited by the wave that introduced it, so a full O(n^2) sweep re-does ~12M
    comparisons to find nothing. Pass --full to force the complete sweep.
    """
    sh = [shingle_set(normalize_tla(r.get("spec_text") or ""), SHINGLE_K) for r in rows]

    def jac(a: set, b: set) -> float:
        return len(a & b) / max(1, len(a | b))

    if since_shard is None:
        pairs = itertools.combinations(range(len(rows)), 2)
    else:
        new = [i for i, r in enumerate(rows) if r["_shard"] >= since_shard]
        new_set = set(new)
        old = [i for i in range(len(rows)) if i not in new_set]
        pairs = itertools.chain(
            ((i, j) for i in new for j in old),
            itertools.combinations(new, 2),
        )

    out = []
    for i, j in pairs:
        v = jac(sh[i], sh[j])
        if v >= NEAR_DUP_THRESHOLD:
            out.append((round(v, 3), rows[i]["seed_key"], rows[j]["seed_key"]))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--full", action="store_true",
                    help="full O(n^2) near-dup sweep instead of the incremental one")
    ap.add_argument("--since", type=int, default=None,
                    help="near-dup floor shard (default: the last two shards)")
    args = ap.parse_args()

    top = max_shard()
    rows = load_effective(top)
    n = len(rows)

    live = sum(1 for r in rows if r.get("liveness_property"))
    safety = n - live

    fams = Counter(
        tag_family((r.get("nl") or "") + " " + (r.get("spec_text") or "")) for r in rows
    )
    top_fam, top_ct = fams.most_common(1)[0]
    top_share = top_ct / max(1, n)

    since = None if args.full else (args.since if args.since is not None else max(0, top - 1))
    dups = near_dups(rows, since)

    ok_total = n >= FLOOR_TOTAL
    ok_live = live >= FLOOR_LIVENESS
    done = ok_total and ok_live

    print(f"shards 0-{top}; effective corpus {n} "
          f"(liveness arm {live}, safety-only {safety})")
    print(f"  total    {n}/{FLOOR_TOTAL} {'MET' if ok_total else f'-- {FLOOR_TOTAL - n} to go'}")
    print(f"  liveness {live}/{FLOOR_LIVENESS} {'MET' if ok_live else f'-- {FLOOR_LIVENESS - live} to go'} "
          f"({100 * live / max(1, n):.1f}% of corpus)")
    print(f"  family   top={top_fam} {top_ct} ({100 * top_share:.1f}%) "
          f"{'OK' if top_share <= FAMILY_MAX_SHARE else f'OVER {100 * FAMILY_MAX_SHARE:.0f}% (advisory)'}")
    print("  families: " + "  ".join(f"{k}={v}" for k, v in fams.most_common()))

    # Surfaced because FIX 1 accepts no_kill/no_site as passes: if real
    # safety_catch stays near zero the mutation gate is not discriminating.
    eviq = Counter(r.get("mutation_evidence") for r in rows)
    catch = eviq.get("safety_catch", 0)
    print(f"  mutation: " + "  ".join(f"{k}={v}" for k, v in eviq.most_common())
          + f"  (real-catch {100 * catch / max(1, n):.1f}%)")

    cfgs = [r.get("cfg_text") or "" for r in rows]
    thin = sum(1 for c in cfgs if len([ln for ln in c.splitlines() if ln.strip()]) <= 3)
    print(f"  cfg: thin(<=3 lines) {thin} ({100 * thin / max(1, n):.1f}%)  "
          f"SPECIFICATION {sum(1 for c in cfgs if 'SPECIFICATION' in c)}  "
          f"CONSTANT {sum(1 for c in cfgs if 'CONSTANT' in c)}  "
          f"PROPERTY {sum(1 for c in cfgs if 'PROPERTY' in c)}")
    scope = "full" if since is None else f"shards>={since}"
    print(f"  near-dups ({scope}): {dups if dups else 'NONE'}")
    print(f"STOP={'YES' if done else 'NO'}")
    return 10 if done else 0


if __name__ == "__main__":
    sys.exit(main())

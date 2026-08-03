"""W4 difficulty probe: measure the base model's per-cell pass rate `p` on the
existing W4 corpus, WITHOUT regenerating a single cell.

Design: docs/designs/2026-08-03-w4-difficulty-probe.md

Why this exists
---------------
W4 has a quality axis and no difficulty axis. `tier` is "complex" on every
tagged row, `complexity_score` is a static structural metric (LOC / variables /
actions), and diamond/gold/silver/bronze grade *mutation kill-rate*. None of
those answer the question that decides whether a training row is worth its
tokens: can the student already do this?

Sancaktar et al. (arXiv:2603.24202) filter synthetic RL problems on empirical
student pass rate -- keep 0.01 < p < 0.97, drop "student never solved". This
module retro-fits the measurement onto the 5,010-row export so the same filter
can be evaluated here.

Scope note: `p = 0` cells are NOT waste under SFT. The paper's "hard problems
starve the reward signal" caveat is GRPO-specific; imitation learning is
precisely the tool for cells the student cannot reach on its own. The only
transferable rule being tested is "drop the p ~= 1 mass".
"""
from __future__ import annotations

import hashlib
import json
import math
import random
from pathlib import Path

from . import w4_corpus

#: Frozen so a re-run reproduces the same sample. Changing it invalidates every
#: number computed against the old sample_frozen.json -- pick a new run-id
#: instead of editing this.
DEFAULT_SEED = 20260803
DEFAULT_N = 300

#: Stratify on both, so the probe can report `p` per training arm AND test
#: whether the mutation-kill tiers carry any difficulty information at all.
STRATUM_FIELDS = ("arm", "tier_name")


def stratum_of(row: dict) -> tuple:
    """The (arm, tier_name) cell a row belongs to."""
    return tuple(row.get(f) for f in STRATUM_FIELDS)


def _largest_remainder(sizes: dict, n: int) -> dict:
    """Allocate `n` across strata proportionally to `sizes`, summing EXACTLY to
    n, capped by each stratum's own size.

    Hamilton's method (floor + largest fractional remainder), then a
    redistribution pass for strata whose quota exceeds their population. Ties
    break on the stratum key so the result is deterministic, not
    dict-order-dependent.
    """
    total = sum(sizes.values())
    if total == 0 or n <= 0:
        return {s: 0 for s in sizes}
    n = min(n, total)

    keys = sorted(sizes)
    alloc = {}
    fracs = []
    for s in keys:
        exact = n * sizes[s] / total
        alloc[s] = int(math.floor(exact))
        fracs.append((exact - alloc[s], s))

    # Hand out the leftover units to the largest fractional remainders.
    shortfall = n - sum(alloc.values())
    for _, s in sorted(fracs, key=lambda t: (-t[0], t[1]))[:shortfall]:
        alloc[s] += 1

    # A stratum can be allocated more than it has. Cap it and re-home the
    # excess into strata that still have headroom, repeatedly -- one pass is
    # not enough when the receiving strata are small too.
    while True:
        excess = sum(max(0, alloc[s] - sizes[s]) for s in keys)
        if excess == 0:
            return alloc
        for s in keys:
            alloc[s] = min(alloc[s], sizes[s])
        headroom = [s for s in keys if alloc[s] < sizes[s]]
        if not headroom:
            return alloc
        # Deterministic round-robin over the strata that can still absorb rows,
        # largest-population first so the spread stays roughly proportional.
        for s in sorted(headroom, key=lambda k: (-sizes[k], k)):
            if excess == 0:
                break
            take = min(excess, sizes[s] - alloc[s])
            alloc[s] += take
            excess -= take
        if excess == 0:
            return alloc


def select_sample(rows: list[dict], n: int = DEFAULT_N,
                  seed: int = DEFAULT_SEED) -> list[dict]:
    """A deterministic, (arm, tier_name)-stratified sample of `n` corpus rows.

    `rows` must already be graded (w4_corpus.grade_corpus), because the strata
    are the graded fields. Rows are sorted by seed_key before sampling so the
    draw does not depend on shard read order.
    """
    missing = [r.get("seed_key") for r in rows if not r.get("tier_name") or not r.get("arm")]
    if missing:
        raise ValueError(
            f"{len(missing)} row(s) are ungraded (e.g. {missing[:3]}); "
            "call w4_corpus.grade_corpus(rows) first"
        )

    buckets: dict[tuple, list[dict]] = {}
    for r in rows:
        buckets.setdefault(stratum_of(r), []).append(r)
    for s in buckets:
        buckets[s].sort(key=lambda r: r["seed_key"])

    alloc = _largest_remainder({s: len(v) for s, v in buckets.items()}, n)

    picked: list[dict] = []
    for s in sorted(buckets):
        k = alloc[s]
        if k <= 0:
            continue
        # A per-stratum RNG keyed on the stratum name: adding a new tier later
        # does not reshuffle the strata that already existed.
        rng = random.Random(f"{seed}:{s[0]}:{s[1]}")
        picked.extend(rng.sample(buckets[s], k))

    picked.sort(key=lambda r: r["seed_key"])
    return picked


def sample_sha256(seed_keys) -> str:
    """Digest over the SORTED, newline-joined seed_keys. Sorted so the hash is
    a property of the SET, not of the order it happened to be written in."""
    body = "\n".join(sorted(seed_keys))
    return hashlib.sha256(body.encode("utf-8")).hexdigest()


def freeze_sample(picked: list[dict], out_path, n: int = DEFAULT_N,
                  seed: int = DEFAULT_SEED,
                  corpus_rows: list[dict] | None = None) -> dict:
    """Write the frozen sample manifest. Every downstream number cites its
    sha256, so this file is append-once: re-freezing under a changed corpus
    produces a different hash and therefore a different run.

    Passing `corpus_rows` (the full graded corpus the sample was drawn from)
    additionally records which strata rounded to zero -- see
    manifest["strata_unsampled"].
    """
    keys = [r["seed_key"] for r in picked]
    strata = {}
    for r in picked:
        arm, tier = stratum_of(r)
        strata.setdefault(f"{arm}/{tier}", 0)
        strata[f"{arm}/{tier}"] += 1

    manifest = {
        "seed": seed,
        "n_requested": n,
        "n_selected": len(keys),
        "strata_counts": dict(sorted(strata.items())),
        "seed_keys": keys,
        "sha256": sample_sha256(keys),
    }
    if corpus_rows is not None:
        # Strata that exist in the corpus but rounded to zero. Proportional
        # allocation is kept deliberately pure -- forcing a floor of 1-2 rows
        # into a 0.14%-of-corpus stratum would bias the pooled estimate and
        # still yield a `p` with no resolution. Recording the omission keeps it
        # visible instead of silent, which is the part that actually matters.
        present = {f"{a}/{t}" for a, t in (stratum_of(r) for r in corpus_rows)}
        manifest["strata_unsampled"] = sorted(present - set(strata))
    out = Path(out_path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


def load_sample(path, rows: list[dict] | None = None) -> tuple[dict, list[dict]]:
    """Read a frozen manifest and re-attach the corpus rows it names.

    Verifies the manifest's own sha256 and that every named key is still in the
    corpus -- a key that vanished means the corpus moved under a frozen sample,
    which invalidates the run rather than merely shrinking it.
    """
    manifest = json.loads(Path(path).read_text())
    recomputed = sample_sha256(manifest["seed_keys"])
    if recomputed != manifest["sha256"]:
        raise ValueError(
            f"sample manifest sha256 mismatch: file says {manifest['sha256']}, "
            f"recomputed {recomputed}"
        )
    if rows is None:
        rows = w4_corpus.grade_corpus(w4_corpus.load_effective())
    by_key = {r["seed_key"]: r for r in rows}
    missing = [k for k in manifest["seed_keys"] if k not in by_key]
    if missing:
        raise ValueError(
            f"{len(missing)} frozen seed_key(s) are no longer in the corpus "
            f"(e.g. {missing[:3]}); the corpus moved under the frozen sample"
        )
    return manifest, [by_key[k] for k in manifest["seed_keys"]]


# --------------------------------------------------------------------- CLI

def _cmd_freeze(a) -> int:
    rows = w4_corpus.grade_corpus(w4_corpus.load_effective())
    if not rows:
        print("FAIL: no corpus rows found (run from the repo root)")
        return 1
    picked = select_sample(rows, n=a.n, seed=a.seed)
    out = Path(a.out)
    if out.exists() and not a.force:
        print(f"FAIL: {out} already exists; a frozen sample is append-once. "
              f"Use a new --run-id, or --force only to regenerate a sample no "
              f"run has cited yet.")
        return 1
    m = freeze_sample(picked, out, n=a.n, seed=a.seed, corpus_rows=rows)
    print(f"corpus {len(rows)} rows -> sample {m['n_selected']}  seed={m['seed']}")
    for s, c in m["strata_counts"].items():
        print(f"  {s:22s} {c}")
    if m.get("strata_unsampled"):
        print(f"  unsampled (rounded to zero): {', '.join(m['strata_unsampled'])}")
    print(f"sha256 {m['sha256']}")
    print(f"wrote {out}")
    return 0


def main(argv=None) -> int:
    import argparse
    ap = argparse.ArgumentParser(prog="python3 -m harness.w4_difficulty")
    sub = ap.add_subparsers(dest="cmd", required=True)

    f = sub.add_parser("freeze", help="draw and freeze the stratified sample")
    f.add_argument("--out", default="results/runs/w4-difficulty-v1/sample_frozen.json")
    f.add_argument("--n", type=int, default=DEFAULT_N)
    f.add_argument("--seed", type=int, default=DEFAULT_SEED)
    f.add_argument("--force", action="store_true",
                   help="overwrite an existing manifest (only safe before any "
                        "run has cited its sha256)")
    f.set_defaults(fn=_cmd_freeze)

    a = ap.parse_args(argv)
    return a.fn(a)


if __name__ == "__main__":
    raise SystemExit(main())

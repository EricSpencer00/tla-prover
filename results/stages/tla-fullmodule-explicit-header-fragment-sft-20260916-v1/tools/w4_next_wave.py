#!/usr/bin/env python3
"""Emit the cell list for the next W4 wave (or a named shard, for backfill).

Run from repo root:

    python3 tools/w4_next_wave.py            # next wave: S_max+1 and S_max+2
    python3 tools/w4_next_wave.py --shard 183  # one shard, for finishing a wave

Exists so the cloud routine prompt does not have to carry a heredoc. Writes
/tmp/shard<S>.txt (one line per cell: key | arm | domain | mechanism | property |
twist) and prints only the shard numbers and cell range.

The arm is a deterministic function of the cell's lattice index parity and is
never reassigned -- even indices are LIVENESS, odd are SAFETY-ONLY.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from harness.w4_scenarios import (  # noqa: E402
    DOMAINS,
    MECHANISMS,
    PROPERTIES,
    TWISTS,
    cell_key,
    lattice,
)

LATTICE_SEED = 20260718
CELLS_PER_SHARD = 25
RUNS = Path("results/runs")


def shard_max() -> int:
    shards = [int(p.name.split("shard")[1]) for p in RUNS.glob("w4-opus-shard*")]
    if not shards:
        raise SystemExit("no w4-opus-shard* dirs under results/runs -- wrong cwd?")
    return max(shards)


def write_shard(s: int) -> Path:
    n = s * CELLS_PER_SHARD
    cells = lattice(LATTICE_SEED, n + CELLS_PER_SHARD)[n:]
    out = Path(f"/tmp/shard{s}.txt")
    with out.open("w") as f:
        for k, c in enumerate(cells):
            arm = "LIVENESS" if (n + k) % 2 == 0 else "SAFETY-ONLY"
            f.write(
                f"  {cell_key(c)} | {arm} | {DOMAINS[c[0]]} | {MECHANISMS[c[1]]}"
                f" | {PROPERTIES[c[2]]} | {TWISTS[c[3]]}\n"
            )
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--shard",
        type=int,
        help="write just this shard (for finishing an incomplete wave)",
    )
    args = ap.parse_args()

    shards = [args.shard] if args.shard is not None else [shard_max() + 1, shard_max() + 2]
    for s in shards:
        write_shard(s)
    lo = shards[0] * CELLS_PER_SHARD
    hi = shards[-1] * CELLS_PER_SHARD + CELLS_PER_SHARD - 1
    print(
        f"wrote /tmp/shard{{{','.join(str(s) for s in shards)}}}.txt"
        f" -- shards {shards[0]}-{shards[-1]}, cells {lo}-{hi}"
    )


if __name__ == "__main__":
    main()

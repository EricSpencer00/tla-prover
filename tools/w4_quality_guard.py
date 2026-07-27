"""W4 wave quality guard -- the abort gate for a looped cheap-model teacher.

Run this after EVERY shard of an unattended generation loop. Exit 0 = keep
going, exit 1 = HALT (a quality metric regressed), exit 10 = stop floors met.

Why this exists
---------------
`w4_audit.py` answers "are we there yet" (row counts vs the stop floors). It
does not answer "is what we are adding still good". Those are different
questions, and they diverge exactly when a weaker/cheaper model drives the
loop: row count climbs on schedule while the corpus quietly degrades. The
three degradation modes the deterministic gate chain CANNOT catch, because
each row passes every gate individually:

  1. Diversity collapse -- a cheap model reaches for the same idioms, so you
     accumulate paraphrases. Note `w4_audit.near_dups` is INCREMENTAL by
     default; a looped weak model is precisely the regime where that is the
     wrong default, so this guard always sweeps the recent window FULL.
  2. Tier collapse -- the model clears easy cells and fails hard ones, so
     diamond+gold share falls while the total looks healthy.
  3. Mutation-signal decay -- `no_kill`/`no_site` are accepted by design
     (w2_loop FIX 1), so a model that writes weak invariants inflates the
     corpus with rows carrying no evidence the invariant catches anything.

Thresholds are floors on the RECENT WINDOW measured against the corpus as it
stands today (2026-07-26: real-catch 12.8%, diamond+gold 82.2%). They are
deliberately set at "do not get worse", not at an aspirational target -- a
guard that fires on the status quo is a guard that gets disabled.
"""
import argparse
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.w4_audit import (  # noqa: E402
    FLOOR_LIVENESS,
    FLOOR_TOTAL,
    RUNS,
    load_effective,
    max_shard,
    near_dups,
)
from harness import w4_corpus  # noqa: E402
from harness.corpus_prep import tag_family  # noqa: E402

# --------------------------------------------------------------------------
# Quality floors on the recent window. Baseline = full corpus at 2026-07-26.
# --------------------------------------------------------------------------
WINDOW_SHARDS = 5          # how many trailing shards count as "recent"
MIN_REAL_CATCH = 0.10      # corpus is 0.128; halt if the window drops below
MIN_DIAMOND_GOLD = 0.75    # corpus is 0.822
MAX_NEAR_DUPS = 0          # any near-dup pair in the window halts the loop
MIN_WINDOW_ROWS = 20       # too few rows to judge -> do not halt on noise


def pct(n: int, d: int) -> float:
    return n / d if d else 0.0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--window", type=int, default=WINDOW_SHARDS,
                    help=f"trailing shards to judge (default {WINDOW_SHARDS})")
    ap.add_argument("--upto", type=int, default=None, help="highest shard to load")
    a = ap.parse_args()

    top = a.upto if a.upto is not None else max_shard()
    rows = load_effective(top)
    since = max(0, top - a.window + 1)
    win = [r for r in rows if r["_shard"] >= since]

    n, wn = len(rows), len(win)
    live = sum(1 for r in rows if r.get("liveness_checked"))
    print(f"corpus {n} rows (liveness {live}); window = shards {since}-{top}, {wn} rows")

    if wn < MIN_WINDOW_ROWS:
        print(f"  window has {wn} rows (<{MIN_WINDOW_ROWS}) -- too few to judge, PASS")
        return 0

    fails = []

    # 1. mutation signal
    catch = sum(1 for r in win if r.get("mutation_evidence") == "safety_catch")
    rc = pct(catch, wn)
    ok = rc >= MIN_REAL_CATCH
    print(f"  real-catch     {100 * rc:5.1f}%  (floor {100 * MIN_REAL_CATCH:.0f}%) "
          f"{'OK' if ok else 'FAIL'}")
    if not ok:
        fails.append(f"real-catch {100 * rc:.1f}% < {100 * MIN_REAL_CATCH:.0f}%")

    # 2. tier mix
    # grade_corpus writes both "tier" (int) and "tier_name" (str); the names
    # are the ones the audit reports, so key off those.
    w4_corpus.grade_corpus(win)
    tiers = Counter(r.get("tier_name") for r in win)
    dg = tiers.get("diamond", 0) + tiers.get("gold", 0)
    dgr = pct(dg, wn)
    ok = dgr >= MIN_DIAMOND_GOLD
    print(f"  diamond+gold   {100 * dgr:5.1f}%  (floor {100 * MIN_DIAMOND_GOLD:.0f}%) "
          f"{'OK' if ok else 'FAIL'}  [" +
          " ".join(f"{k}={v}" for k, v in tiers.most_common()) + "]")
    if not ok:
        fails.append(f"diamond+gold {100 * dgr:.1f}% < {100 * MIN_DIAMOND_GOLD:.0f}%")

    # 3. diversity -- FULL sweep of the window against everything
    dups = near_dups(rows, since_shard=since)
    ok = len(dups) <= MAX_NEAR_DUPS
    print(f"  near-dups      {len(dups):5d}   (max {MAX_NEAR_DUPS}) "
          f"{'OK' if ok else 'FAIL'}")
    for d in dups[:5]:
        print(f"      {d[0]}  {d[1]}  {d[2]}")
    if not ok:
        fails.append(f"{len(dups)} near-dup pair(s) in window")

    # advisory: family skew of the window (informs the NEXT shard's targeting)
    fams = Counter(tag_family((r.get("nl") or "") + " " + (r.get("spec_text") or ""))
                   for r in win)
    if fams:
        tf, tc = fams.most_common(1)[0]
        print(f"  window family  top={tf} {tc} ({100 * pct(tc, wn):.1f}%) [advisory]")

    if fails:
        print("\nHALT -- " + "; ".join(fails))
        print("Do not queue another shard until the teacher config is fixed.")
        return 1

    if n >= FLOOR_TOTAL and live >= FLOOR_LIVENESS:
        print(f"\nSTOP -- floors met ({n}/{FLOOR_TOTAL}, {live}/{FLOOR_LIVENESS}).")
        return 10

    print(f"\nCONTINUE -- quality holding; {max(0, FLOOR_TOTAL - n)} rows / "
          f"{max(0, FLOOR_LIVENESS - live)} liveness to go.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

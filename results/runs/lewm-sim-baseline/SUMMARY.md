# LEWM Open-Question-3 falsifiable baseline: TLC `-simulate` vs BFS

2026-07-21. Non-learned baseline measurement, run BEFORE any learned fail-fast
triage model (docs/designs/2026-07-20-lewm-tlc-requirements.md) is justified.
Question: does TLC's built-in `-simulate` (random-walk) mode find violations
faster than BFS model-checking on the recorded slow/timeout/injected
candidates, with zero training and zero learned components?

## Method

- Manifest: `results/analysis/lewm_baseline_candidates.json` (326 rows).
- 123 rows have `candidate_recoverable=true`; deduped by candidate-file
  sha256, these collapse to **77 unique candidate files** (many manifest rows
  point at byte-identical candidates re-scored across different sweep runs).
- Each unique candidate was run under `java ... tlc2.TLC -simulate
  num=100000 -depth 100 -seed <s>` for seeds 0, 1, 2, wall-capped at 120s per
  seed (killed on cap), using the exact classpath / `-DTLA-Library` /
  isolated `java.io.tmpdir` conventions in `harness/runner.py` (imported
  read-only, not modified) and the same cfg-resolution precedence
  (override > original > draft) plus per-spec `policy.json` wrapper/flags
  handling.
- Script: `tools/lewm_sim_baseline.py`. Raw per-(candidate, seed) results:
  `results/runs/lewm-sim-baseline/rows.jsonl` (231 rows = 77 x 3, full
  coverage, no gaps -- resumable dedup key is (candidate_sha256, seed)).

## Per-bucket outcome table

Bucket is the union of the manifest's `bucket` field(s) across all manifest
rows that dedup to the same candidate file (a handful of candidates were
independently re-scored in multiple sweep runs and landed in different
buckets each time -- shown as `a+b`).

| manifest bucket(s) | n candidates | -simulate: no_violation | -simulate: timeout (120s cap) | -simulate: violation found | -simulate: error (SANY/semantic) |
|---|---|---|---|---|---|
| `timeout` | 3 | 0 | 6 | 3 | 0 |
| `slow_fail` | 2 | 0 | 3 | 0 | 3 |
| `slow_fail+slow_pass` | 1 | 0 | 3 | 0 | 0 |
| `slow_other:error+slow_pass+timeout` | 1 | 3 | 0 | 0 | 0 |
| `slow_pass` | 70 | 117 | 84 | 0 | 9 |
| all | 77 | 120 | 96 | 3 | 12 |

(counts are seed-runs, 3 per candidate = 231 total.)

## Headline

Of the candidates in the `timeout` bucket (BFS timed out) that are also
flagged `known_broken_elsewhere` in the manifest -- the actual population
this experiment is meant to speak to -- there are K = 3 unique candidates.
`-simulate` found a violation on M = 1 of those 3 (spec 30, all 3 seeds
converged on the same invariant violation), with median time-to-violation
approx 0.43s (wall-clock across the 3 seeds: 0.40s, 0.43s, 0.58s) versus
BFS's 120s+ timeout -- roughly a 200-280x speedup on the one candidate where
it worked.

The other 2 of the 3 known-broken timeout candidates did NOT convert: spec
14's candidate ran to completion with `no_violation` in ~29s (all 3 seeds;
not a timeout at all under `-simulate` -- the BFS timeout there may be a
genuinely different bottleneck, e.g. state-space breadth vs. `-simulate`'s
depth-100 random walk not exploring the same region), and spec 141's
candidate also timed out under `-simulate` at the full 120s cap on all 3
seeds -- the failure mode is not sensitive to search strategy for that
candidate.

## Honest null

This is a small-N, mostly-null result. M=1/K=3 is not enough to claim
`-simulate` is a reliable fail-fast triage signal; it is enough to falsify
the strong version of the hypothesis ("`-simulate` reliably converts BFS
timeouts to fast violations") -- it does not. It converted exactly one
candidate, and that one had a shallow, cheap-to-hit invariant violation
(found within seconds regardless of seed, suggesting a broad basin, not a
narrow one that needed random search to find). The other timeout-bucket
candidates were either not actually slow under `-simulate` (spec 14, but for
a different reason -- no violation, not speed) or equally intractable (spec
141, still timed out).

Zoomed out to all 77 unique candidates regardless of bucket: 120/231 (52%)
seed-runs found no violation within the num=100000/depth=100 walk, 96/231
(42%) hit the 120s wall-clock cap without finishing that walk, 3/231 (1%)
found a violation, and 12/231 (5%) errored -- all 12 error rows are genuine
SANY/TLC semantic-parse failures in the candidate text itself (e.g. a
model-generated `MCBoulanger.tla` for spec 14 that multiply-defines
`NatOverride`), not script or invocation bugs; confirmed by manual TLC
re-invocation outside this script showing identical `Operator ... already
defined or declared` output. (Note in passing: a few of those 12 error rows'
manifest `tlc_classification` says "pass" -- that looks like a pre-existing
mismatch in the manifest, upstream of and out of scope for this experiment;
this script's own direct TLC invocation is self-consistent and is what the
numbers above reflect.)

Bottom line: `-simulate` is not a free lunch for TLC fail-fast triage on this
candidate population. It found 1 real conversion out of 3 known-broken
timeouts, at a real (if narrow) 200x+ speedup when it worked, but the
majority of the timeout population it left untouched -- either because the
failure isn't reachable by random walk within the depth/seed budget tried,
or because the "slowness" isn't really about search strategy. This is
exactly the kind of null result Q3 was designed to either confirm or falsify
a naive hope of "just run -simulate instead of learning anything" -- it
falsifies it as a general solution, while leaving a narrow, real signal
(fast wins on some invariant-violation candidates) that a learned
prioritizer could plausibly build on rather than replace.

## Coverage check

- 123 recoverable manifest rows -> 77 unique candidate files after sha256
  dedup (0 candidates skipped for missing/unrecoverable cfg -- every
  recoverable candidate's spec number resolved a cfg via
  `/Users/eric/GitHub/tla_benchmark/data/cfg/{spec}.cfg`, the corpus root
  recorded in the originating run's `config.json`).
- 77 candidates x 3 seeds = 231 expected rows; `rows.jsonl` has exactly 231
  rows, 0 duplicate (sha, seed) pairs -- full coverage, nothing missing.

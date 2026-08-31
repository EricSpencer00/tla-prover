# W4 corpus re-audit, seed-1 and seed-2 replications (2026-08-31)

The 2026-08-30 re-audit (`w4_recall_audit_2026-08-30.md`) sampled 30 specs per
ledger stratum at seed 0. This repeats it at seed 1 and seed 2 to test whether
0.19 is a sample accident. The three samples share 2 specs per pair and cover
265 distinct specs, so each seed is a near-independent draw from the same corpus.

Run: `python3 tools/w4_recall_audit.py --seed N` (30 specs per stratum, 60s
timeouts, 90 specs per seed). Rows: `w4_recall_audit_2026-08-30_seed1_rows.jsonl`,
`w4_recall_audit_2026-08-31_seed2_rows.jsonl`. Logs alongside them.

## Result

| stratum | corpus | n (per seed) | covered | recall_miss | no_evidence | real catch | reproduced |
|---|---|---|---|---|---|---|---|
| no_kill (seed 1) | 3,169 | 30 | 0 | 19 | 11 | 19/30 = 63% | 30/30 |
| no_site (seed 1) | 1,200 | 30 | 0 | 21 | 9 | 21/30 = 70% | 30/30 |
| safety_catch (seed 1) | 641 | 30 | 22 | 0 | 8 | 22/30 = 73% | 30/30 |
| no_kill (seed 2) | 3,169 | 30 | 0 | 19 | 11 | 19/30 = 63% | 30/30 |
| no_site (seed 2) | 1,200 | 30 | 0 | 20 | 10 | 20/30 = 67% | 30/30 |
| safety_catch (seed 2) | 641 | 30 | 23 | 0 | 7 | 23/30 = 77% | 30/30 |

| sample | corpus-weighted recall | 95% CI | rows with a demonstrable catch |
|---|---|---|---|
| seed 0 | 0.19 | [0.15, 0.23] | 3,107 / 5,010 = 62% |
| seed 1 | 0.14 | [0.11, 0.18] | 3,317 / 5,010 = 66% |
| seed 2 | 0.15 | [0.12, 0.19] | 3,298 / 5,010 = 66% |
| pooled (n=270) | **0.16** | [0.14, 0.18] | 3,241 / 5,010 = 65% |

Floor is 0.50. All three samples FAIL, the CIs overlap, and the pooled upper
bound is 0.18. The 0.19 was not a seed accident.

Controls repeat on every seed. The safety_catch arm reads recall 1.00 each time,
so the probe set has power. 270/270 specs re-run to their own ledger label, so
the ledger is a faithful record of the battery.

Missing operators, pooled: `bound_shift` 78, `guard_relax` 41, `cmp_relax` 32,
`conj_to_disj` 1. Same order on each seed.

## What this changes

Nothing. The stop floors do not read `mutation_evidence` (`tools/w4_audit.py`
gates on `FLOOR_TOTAL` and `FLOOR_LIVENESS` only), so floors-MET at 5,010 rows
stands. `w4_corpus.grade_row`'s DIAMOND tier still under-counts strong rows by
about 4x. Promoting the three operators into `mutation.MUTATIONS` is still
Eric's call.

Bound, unchanged: the probes never touch a cfg-checked definition while the
whole-module battery does, so these numbers are an upper bound on battery recall.

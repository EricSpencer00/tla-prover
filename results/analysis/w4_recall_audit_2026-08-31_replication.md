# W4 corpus re-audit, seed-1 replication (2026-08-31)

The 2026-08-30 re-audit (`w4_recall_audit_2026-08-30.md`) sampled 30 specs per
ledger stratum at seed 0. This repeats it at seed 1 to test whether 0.19 is a
sample accident. The two samples share 2 of 180 specs, so seed 1 is an
independent draw from the same corpus.

Run: `python3 tools/w4_recall_audit.py --seed 1` (30 specs per stratum, 60s
timeouts, 90 specs). Rows: `w4_recall_audit_2026-08-30_seed1_rows.jsonl`. Log:
`w4_recall_audit_2026-08-30_seed1.log`.

## Result

| stratum | corpus | n | covered | recall_miss | no_evidence | real catch | reproduced |
|---|---|---|---|---|---|---|---|
| no_kill | 3,169 | 30 | 0 | 19 | 11 | 19/30 = 63% | 30/30 |
| no_site | 1,200 | 30 | 0 | 21 | 9 | 21/30 = 70% | 30/30 |
| safety_catch | 641 | 30 | 22 | 0 | 8 | 22/30 = 73% | 30/30 |

| sample | corpus-weighted recall | 95% CI | rows with a demonstrable catch |
|---|---|---|---|
| seed 0 | 0.19 | [0.15, 0.23] | 3,107 / 5,010 = 62% |
| seed 1 | **0.14** | [0.11, 0.18] | 3,317 / 5,010 = 66% |
| pooled (n=180) | **0.16** | [0.14, 0.19] | 3,212 / 5,010 = 64% |

Floor is 0.50. Both samples FAIL, the CIs overlap, and the pooled upper bound is
0.19. The 0.19 was not a seed accident.

Controls repeat. The safety_catch arm reads recall 1.00 again, so the probe set
has power. 90/90 specs re-run to their own ledger label again (180/180 across
both seeds), so the ledger is a faithful record of the battery.

Missing operators at seed 1: `bound_shift` 29, `guard_relax` 16, `cmp_relax` 11,
`conj_to_disj` 1. Same order as seed 0.

## What this changes

Nothing. The stop floors do not read `mutation_evidence`, so floors-MET at 5,010
rows stands. `w4_corpus.grade_row`'s DIAMOND tier still under-counts strong rows
by about 4x. Promoting the three operators into `mutation.MUTATIONS` is still
Eric's call.

Bound, unchanged: the probes never touch a cfg-checked definition while the
whole-module battery does, so these numbers are an upper bound on battery recall.

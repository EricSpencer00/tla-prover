# W4 corpus re-audit against the mutation-recall gate (2026-08-30)

The 5,010-row effective corpus was declared floors-MET while reading
`mutation_evidence` written by a battery that
`results/analysis/mutation_recall_gate_2026-08-30.md` then measured at 0.12
operator recall. This re-scores the corpus itself.

Run: `python3 tools/w4_recall_audit.py` (30 specs per stratum, seed 0, 60s
timeouts, 90 specs). Rows: `w4_recall_audit_2026-08-30_rows.jsonl`. Log:
`w4_recall_audit_2026-08-30.log`.

## Result

| stratum | corpus | n | covered | recall_miss | no_evidence | real catch (95% CI) |
|---|---|---|---|---|---|---|
| no_kill | 3,169 | 30 | 0 | 16 | 14 | 16/30 = 53% [36, 70] |
| no_site | 1,200 | 30 | 0 | 21 | 9 | 21/30 = 70% [52, 83] |
| safety_catch | 641 | 30 | 27 | 0 | 3 | 27/30 = 90% [74, 97] |

Corpus-weighted operator recall **0.19** (bootstrap 95% CI [0.15, 0.24]), floor
0.50 — **FAIL**. The 0.12 the gate measured on two 12-spec arms holds for the
whole corpus.

Read per stratum, recall is 0.00 on no_kill and no_site by construction:
`covered` needs a battery kill, and those strata are defined by the battery not
killing. The corpus-weighted number is the one that means something.

**An estimated 3,107 of 5,010 rows (62%) have an invariant that demonstrably
catches a semantic corruption.** The ledger credits 641 (13%). The battery misses
the other ~2,530.

Missing operators, by recall_miss specs killed: `bound_shift` 24, `guard_relax`
12, `cmp_relax` 8. `conj_to_disj` killed on no missed spec on its own.

## Two controls

- **safety_catch arm.** 27/30 covered, recall 1.00. The probe set finds what the
  battery finds, so the 0.19 is battery recall and not a broken probe.
- **Ledger reproduction.** 90/90 specs re-run to the same `mutation_evidence`
  the ledger holds. The ledger is a faithful record of the battery. The battery
  is what is weak.

## What this changes, and what it does not

**Stop floors stand.** `tools/w4_audit.py` gates on `FLOOR_TOTAL` 5,000 and
`FLOOR_LIVENESS` 500. Neither reads `mutation_evidence`. Floors-MET at 5,010 rows
and 567 liveness rows does not depend on the battery, so the re-audit does not
move it.

**Tier grading is what the weak battery distorts.** `w4_corpus.grade_row` makes
DIAMOND mean "the battery caught a mutant". At 0.19 recall that tier is a sample
of strong rows, not the set of them: it under-counts by about 4.8x. The GOLD
docstring already assumed absence of a catch is absence of evidence; this
measures that assumption and it holds for 62% of the weak-labelled rows. For the
other 38% the probes found nothing either, which is still not evidence of
weakness.

Consequence for the pre-registered eval: `sft_w4_diamond_gold_5010.jsonl` merges
diamond and gold, so it is unaffected. Any diamond-ONLY arm is drawing from a
13% sample of a 62% population, and a diamond-vs-gold comparison measures battery
recall as much as spec strength. That comparison should not be run on the
current tiers.

## Not done

Promoting `bound_shift`, `guard_relax` and `cmp_relax` into `mutation.MUTATIONS`
re-scores every ledgered survivor and moves rows from gold to diamond. It is a
corpus decision, not a harness fix, and it is Eric's call. The numbers above are
what it would cost to keep deferring it: roughly 2,530 rows mis-tiered.

Bound, unchanged from the gate: the probes never touch a cfg-checked definition
while the whole-module battery does, so 0.19 is an upper bound on battery recall.

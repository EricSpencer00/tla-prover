# E2.c Gate-2 baseline — audited results (2026-07-07)

Source: `results/runs/e2c-baseline-{20b,120b}-{a,b}` (commit e9523dd). Frozen
30-spec holdout (`corpus/holdout_30.json`, sha256 `ecfc2053...4f78`), Amendment-12
budget (temp 0.8, max_tokens 16384, TLC 120s serial, k=32 -> 33 samples/spec incl.
greedy). Audit method and scope: `results/runs/SEMAUDIT_FINDINGS.md` ("E2.c
Gate-2 baseline" section) — **read that section before treating these numbers as
final**; the short version: verdicts are audited against every *mechanical*
reward-hack channel the harness records (vacuity, cfg substitution, criterion
mismatch) but candidate module text was not persisted by `gen_eval.py`, so a
diff-based check for subtle semantics-narrowing repairs (the Stage-1 `semaudit.py`
method) was not possible. 0 rows were rejected; 1 row was flagged and confirmed
not-a-false-pass (spec 142/120b-a/sample 19, proof_module type, TLC vacuity
irrelevant to its tlaps-keyed verdict). 0 `api_error` rows in any arm.

## Framing A — NL description -> generate a TLA+ module (N = 30 specs)

| model | pass@1 | pass@32 |
|---|---|---|
| gpt-oss-20b  | 0/30 (0.0%)  | 4/30 (13.3%) |
| gpt-oss-120b | 2/30 (6.7%)  | 12/30 (40.0%) |

- 20b-a pass@32 specs: 5, 86, 142, 183
- 120b-a pass@1 specs: 30, 41
- 120b-a pass@32 specs: 2, 5, 30, 37, 41, 86, 95, 105, 131, 142, 143, 183

**Best arm, framing A: gpt-oss-120b** (both pass@1 and pass@32).

## Framing B — corrupted module -> repair (N = 23 valid specs; 7 ledgered skips)

7 specs (41, 86, 105, 106, 133, 135, 183) have **no valid corruption** under
`find_valid_corruption` (every deterministic mutation site either fails SANY or
the corrupted text still passes the criterion) — ledgered as
`skipped:no_valid_corruption` rows, identical across both models (corruption is
spec-only, model-independent). These are excluded from the framing-B denominator
below; fractions are out of 23.

| model | pass@1 | pass@32 |
|---|---|---|
| gpt-oss-20b  | 6/23 (26.1%)  | 22/23 (95.7%) |
| gpt-oss-120b | 14/23 (60.9%) | 21/23 (91.3%) |

- 20b-b pass@1 specs: 2, 13, 37, 132, 158, 181
- 20b-b pass@32 specs: 2, 5, 13, 14, 15, 30, 32, 37, 55, 95, 121, 128, 131, 132, 141, 143, 148, 158, 168, 174, 181, 191 (22/23 valid specs — only miss is spec 142, a genuine framing-B fail for gpt-oss-20b, not a skip)
- 120b-b pass@1 specs: 2, 5, 13, 14, 32, 37, 95, 128, 132, 148, 158, 168, 181, 191
- 120b-b pass@32 specs: 2, 5, 13, 14, 30, 32, 37, 55, 95, 121, 128, 131, 132, 141, 143, 148, 158, 168, 174, 181, 191

**Best arm, framing B pass@1: gpt-oss-120b (14/23).**
**Best arm, framing B pass@32: gpt-oss-20b (22/23), narrowly over gpt-oss-120b (21/23)** —
note this is a pass@32 (any-of-32) inversion vs. pass@1, where 120b leads by a
wide margin; both are close to ceiling for framing B (repair task, given a
minimal single-site corruption, is easier than framing A's from-scratch
generation for both models).

## Skip ledger (framing B, both models — spec-only, not model-dependent)

Specs with `skipped:no_valid_corruption`: 41, 86, 105, 106, 133, 135, 183 (7 of
the 30 holdout specs). These specs' single-mutation-site corruptions never
produced a SANY-passing + criterion-failing candidate under
`find_valid_corruption`'s full ring-walk of every candidate site — not a model
result, a corpus/mutation-coverage gap. Excluded from framing-B N (23 valid).

## Evidence integrity notes

- **0 `api_error` rows** across all 4 arms (searched `verdict` and
  `budget_used` fields) — no polluted rows requiring quarantine.
- **`logs/` are not committed** (gitignored) and, for this harness path
  (`gen_eval.run_gen_eval`), are overwritten per-sample rather than appended —
  the log for a given spec reflects only the LAST sample scored for it, not
  each of the 33. This is a pre-existing harness limitation (not specific to
  this run) and does not affect the row-level verdicts, which were each
  computed and recorded independently at scoring time.
- **No candidate module text was persisted** for any of the 3512 rows across
  the 4 arms (see SEMAUDIT_FINDINGS.md E2.c section for the full scope
  disclosure). This is the primary residual audit gap for this baseline.

## Draft freeze artifact

`corpus/e2c_baseline.DRAFT.json` mirrors this table in machine-readable form.
**Not** `corpus/e2c_baseline.json` — final freeze requires Eric's sign-off per
the E2.c handoff (PLAN.md Amendment 12 wording is the coordinator's to write).

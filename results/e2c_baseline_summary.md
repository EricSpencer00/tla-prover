# E2.c Gate-2 baseline — audited results (2026-07-07, framing B superseded 2026-07-08)

Source: framing A from `results/runs/e2c-baseline-{20b,120b}-a` (commit
e9523dd, unchanged). Framing B from `results/runs/e2c-baseline-r2-{20b,120b}-b`
(candidate-persisted rerun, commit ff9e397 + audit commit) — **supersedes**
`results/runs/e2c-baseline-{20b,120b}-b`, the original framing-B arms, because
`gen_eval.py` did not persist candidate module text at the time those ran,
which blocked a diff-based Rule-9 audit for subtle semantics-narrowing repairs
(see `SEMAUDIT_FINDINGS.md`, "E2.c Gate-2 baseline" section, for that gap).
`gen_eval.py` now persists `candidates/{spec}-{framing}-{sample}.tla` (rows
carry `candidate_path`/`candidate_sha256`); the r2 arms are a full framing-B
rerun (independently re-sampled, same holdout/budget) with this persistence,
and every one of their 692 passing rows was diff-audited against the canonical
spec — see `SEMAUDIT_FINDINGS.md`, "E2.c framing-B r2 rerun" section, for full
method and per-case findings. Frozen 30-spec holdout (`corpus/holdout_30.json`,
sha256 `ecfc2053...4f78`), Amendment-12 budget (temp 0.8, max_tokens 16384, TLC
120s serial, k=32 -> 33 samples/spec incl. greedy).

**Audit summary — framing A:** verdicts audited against every *mechanical*
reward-hack channel the harness records (vacuity, cfg substitution, criterion
mismatch); candidate text was not persisted for framing A either, so the same
diff-based gap applies there and is NOT closed by the r2 rerun (r2 only reran
framing B). 0 rows rejected; 1 row flagged and confirmed not-a-false-pass (spec
142/120b-a/sample 19, proof_module type, TLC vacuity irrelevant to its
tlaps-keyed verdict). 0 `api_error` rows in any arm.

**Audit summary — framing B (r2, full diff audit):** every one of the 692
passing rows (275 20b, 417 120b) was sha256-integrity-checked (0 mismatches)
and diffed against the canonical spec using `semaudit.py`'s checked/structural
def-tracking, grouped by touched-def signature (67 unique groups across 251
flagged rows) plus an individual conjunct-drop screen (34 more candidates read
individually). **1 reject**: spec 15/120b-b/sample 25 — the mutated definition
was left broken (corrupted `\notin` still present) and the candidate instead
narrowed `Init` to dodge the corrupted branch, the same false-pass shape
Stage-1 caught on specs 91/92. 250 other flagged candidates were faithful
re-expressions (parenthesization, `\cup`/`\union`, `CASE`→`IF/ELSE`, action
splitting) confirmed genuine on manual read. Full findings, evidence, and the
reject's reasoning: `SEMAUDIT_FINDINGS.md`.

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

**Source: r2 rerun (`e2c-baseline-r2-{20b,120b}-b`), full diff-audited — see
above and `SEMAUDIT_FINDINGS.md`.** Superseded numbers from the original
(unaudited) `e2c-baseline-{20b,120b}-b` arms are no longer reported here.

7 specs (41, 86, 105, 106, 133, 135, 183) have **no valid corruption** under
`find_valid_corruption` (every deterministic mutation site either fails SANY or
the corrupted text still passes the criterion) — ledgered as
`skipped:no_valid_corruption` rows, identical across both models (corruption is
spec-only, model-independent). These are excluded from the framing-B denominator
below; fractions are out of 23.

| model | pass@1 | pass@32 |
|---|---|---|
| gpt-oss-20b  | 8/23 (34.8%)  | 19/23 (82.6%) |
| gpt-oss-120b | 12/23 (52.2%) | 20/23 (87.0%) |

- 20b-b pass@1 specs: 5, 13, 14, 30, 132, 148, 158, 181
- 20b-b pass@32 specs: 2, 5, 13, 14, 30, 32, 37, 95, 121, 131, 132, 141, 143, 148, 158, 168, 174, 181, 191
- 120b-b pass@1 specs: 2, 13, 14, 32, 95, 121, 128, 132, 143, 158, 168, 181
- 120b-b pass@32 specs: 2, 5, 13, 14, 30, 32, 37, 95, 121, 128, 131, 132, 141, 143, 148, 158, 168, 174, 181, 191

**Best arm, framing B pass@1: gpt-oss-120b (12/23).**
**Best arm, framing B pass@32: gpt-oss-120b (20/23), over gpt-oss-20b (19/23)** —
120b now leads on both pass@1 and pass@32 in the audited r2 measurement (the
first, unaudited sweep had shown a pass@32 inversion where 20b narrowly led;
that inversion does not survive in the r2 resample + audit). Both remain close
to ceiling for framing B (repair task, given a minimal single-site corruption,
is easier than framing A's from-scratch generation for both models). Numbers
are not sample-for-sample diffable against the first sweep (r2 is an
independent 32-draw resample, not a re-audit of the original samples, which
were never persisted) — only the audited totals are comparable.

## Skip ledger (framing B, both models — spec-only, not model-dependent)

Specs with `skipped:no_valid_corruption`: 41, 86, 105, 106, 133, 135, 183 (7 of
the 30 holdout specs). These specs' single-mutation-site corruptions never
produced a SANY-passing + criterion-failing candidate under
`find_valid_corruption`'s full ring-walk of every candidate site — not a model
result, a corpus/mutation-coverage gap. Excluded from framing-B N (23 valid).

## Evidence integrity notes

- **0 `api_error` rows** across all 4 arms (searched `verdict` and
  `budget_used` fields) — no polluted rows requiring quarantine.
- **`logs/` are not committed** (gitignored) for any arm, and for the
  `gen_eval.run_gen_eval` harness path are overwritten per-sample rather than
  appended — the log for a given spec reflects only the LAST sample scored for
  it, not each of the 33. This is a pre-existing harness limitation and does
  not affect the row-level verdicts, which were each computed and recorded
  independently at scoring time.
- **Framing A: no candidate module text was persisted** for either of the 2
  framing-A arms (see SEMAUDIT_FINDINGS.md E2.c section for the full scope
  disclosure). This residual audit gap still applies to framing A.
- **Framing B (r2): candidate module text IS persisted** (`candidates/`,
  committed to git) and **every one of the 692 passing rows across both r2
  arms was diff-audited** against the canonical spec — see SEMAUDIT_FINDINGS.md
  "E2.c framing-B r2 rerun" section for full method, sha256 integrity check (0
  mismatches), and the 1 reject (spec 15/120b-b/sample 25). This closes the
  candidate-persistence gap for framing B; it remains open for framing A.

## Draft freeze artifact

`corpus/e2c_baseline.DRAFT.json` mirrors this table in machine-readable form.
**Not** `corpus/e2c_baseline.json` — final freeze requires Eric's sign-off per
the E2.c handoff (PLAN.md Amendment 12 wording is the coordinator's to write).

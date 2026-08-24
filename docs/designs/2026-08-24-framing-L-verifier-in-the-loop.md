# Framing L: the verifier IN the loop, at framing A's model-call budget

Pre-registered 2026-08-24, before any endpoint call. Nothing below is tuned
against an outcome; the policy constants are fixed here and the analysis rule is
stated before the run.

## The question

Every framing-A arm this project has measured is **open-loop**: k independent
draws from one prompt, each scored, best-of reported. The compiler is a judge and
never a controller. The locked north star says the opposite — correctness comes
from the verify LOOP, not the weights — so the central number has never actually
been measured.

## What the existing ledgers already say (re-scored 2026-08-24, best arm `gate2-w4dgm-120b-A`, 990 rows)

| | per-sample | any-of-33 |
|---|---|---|
| SANY parse | 29.3% | **28/30 (93%)** |
| parse + every .cfg identifier defined | — | **26/30 (87%)** |
| TLC pass | 6.0% | **11/30 (37%)** |

Failure mass, 990 draws: 70.7% never parse; of the 290 that do, 192 hit a TLC
*error* and only 29 draws in the whole run (2.9%) fail on a genuine property
violation. **The failure is mechanics, not modeling.**

Two prior results bound what to expect:

- **Syntax alone is not the lever.** `tools/lint_repair_probe.py` deterministically
  forced 88 candidates across 9 unsolved specs from fail→parse;
  `lint_repair_tlc.py` then scored them: **0 specs flipped**. All 88 died at TLC.
- **The interface is a third of the remaining wall, and is free to detect.** A
  signature checker (does the module provide every identifier the fixed .cfg
  names?) validated against 169 real TLC-passing candidates has **0 false
  positives**, never flags a genuine violation, and catches **27% of tlc=error
  candidates with zero tool calls**. It is wired as a feedback selector, never as
  a gate: nothing is allowed to skip a verification stage.

## Design — 2x2, equal model-call budget, one frozen 30-spec holdout

| | open-loop (already measured) | closed-loop (to run) |
|---|---|---|
| base `gpt-oss-120b` | `e2c-baseline-120b-a` = **12/30** | **ARM L-base** |
| `chattla-w4dgm-120b` (best arm) | `gate2-w4dgm-120b-A` = **15/30** | **ARM L-tuned** |

Both open-loop cells are re-scored from `rows.jsonl`, not from `summary.json`
(the baseline's committed summary says 1/30 and is stale).

**Budget.** Framing A spends 33 model calls per spec (1 greedy + k=32). Framing L
is given **8 chains x 4 rounds = 32** — deliberately fewer, so the loop never wins
on budget. Enforced in code and pinned by `test_budget_is_exactly_chains_times_rounds_when_never_passing`.

**Concurrency.** The chains advance in LOCK STEP: each round issues one model call
per chain, all concurrently (`GEN_EVAL_CONCURRENCY`), then scores the replies one at
a time in chain order. TLC stays strictly serialized -- only network calls overlap,
exactly as in `gen_eval._prefetch_replies`. This is not a nicety: framing A's calls
have a median `model_s` of 27.8s, so a serial 32-call chain would cost ~8h of pure
generation for 30 specs and would not fit one 6h serve window. Lock-step puts it
near 1h.

**Chain.** Round 0 of every chain generates from the framing-A generation prompt, **byte-identical**
(pinned by `test_round0_prompt_is_byte_identical_to_framing_a`, and checkable after
the fact because the ledger records `prompt_sha256`). Rounds 1-3 repair the previous
round's candidate from its own diagnosis. Chain 0 round 0 is greedy@0; every other
call is temp 0.8. A chain whose reply yields no module is abandoned and the next
round regenerates from the framing-A prompt rather than stalling, so the budget is
always spent on either depth or diversity.

**Diagnosis rungs**, priority order — the rung decides what the next prompt says:
`signature` > `sany` > `tlc_error` > `tlc_violation`.

**Scoring** is `gen_eval._score` verbatim: same SANY/TLC/TLAPS stages, same
timeouts, same `verdict_of`. An L row is comparable to an A row by construction.

## Controls

1. **Feedback ablation** — the framing-A arms themselves: same prompt, same
   scorer, same-or-larger budget, no error text. This is the control that
   separates "the feedback did something" from "more samples did something".
2. **Positive control on the accept path** — replay the corpus's own spec text
   through the loop; it must accept in one call. Run 2026-08-24 on specs 2, 5, 37,
   181 against real SANY/TLC: 4/4 accepted in one call.
3. **Positive control on the feedback path** — same specs with one required
   identifier deleted: the loop must diagnose it, name it in the round-1 prompt,
   and recover. 4/4 recovered.
4. **Signature-checker false-positive control** — 169 TLC-passing candidates,
   0 flagged (see above).

## Analysis rule, fixed before the run

The measured noise floor for single-run spec-level pass@32 is about +/-1-2 specs
(`docs/W4DG_GATE2_SESSION_2026-07-29.md` section 2: 17 byte-identical prompts
moved 1 spec across A->A3 while row-level counts swung 5->1 and 7->12). So:

- **L counts as a win over its open-loop control only at >= +5 specs, or paired
  McNemar exact p < 0.05.** A +2 is reported as null.
- Secondary, reported regardless: calls-to-solve distribution, which rung each
  solved spec was rescued from, and per-sample SANY/TLC rates for comparability
  with every prior arm.
- Every arm is re-scored with `harness gate-check` from `rows.jsonl`. `summary.json`
  is never the source.

## What each outcome means

- **L-base >= 15/30** (matches or beats the best fine-tune, open-loop): the
  fine-tuning program is not the lever. Stop spending on weights; spend on the loop.
- **L-tuned >> L-base**: the tuning bought repairability rather than generation,
  which is what Amendment 25 already hints at (repair restored to baseline).
- **Both flat**: the loop does not help open-loop failures, the 15-spec gap
  between "mechanically complete" (26/30) and "model-checks" (11/30) is genuine
  modeling failure after all, and direction 3 from the 2026-08-12 call
  (planner->generator) becomes the right next lever rather than the deferred one.

## Run commands

```
python3 tools/smoke/serve_preflight.py --model <served-id> --max-tokens 16384
python3 -m harness loop-eval --model openai:<served-id> --run-id loop-<arm> --chains 8 --rounds 4
python3 -m harness gate-check results/runs/loop-<arm>
```

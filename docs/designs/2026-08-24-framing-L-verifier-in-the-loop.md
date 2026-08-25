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
5. **Feedback-quality audit on real failures**, run before any endpoint call:
   all 876 failing candidates in `gate2-w4dgm-120b-A` were put through
   `diagnose()` + `localize()`. Evidence was never empty. Rungs: sany 580 (66%),
   signature 171 (20%), tlc_error 96 (11%), tlc_violation 29 (3%) -- the same
   mechanics-dominated shape the ledger shows. Localization produced a fragment
   for 95% of parse errors; the 228 empty fragments were 171 `signature` rows
   (which have no error location by construction -- the identifier is missing)
   plus 26 tlc_error and 30 sany. **Prompt change made as a result, before any
   arm was run:** the `signature` rung now falls back to the module's
   declaration block instead of "(the error did not localize to a definition)",
   so 20% of feedback messages stop being content-free.

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

## Result — ARM L-base, 3 seeds vs 3 control seeds, measured 2026-08-24/25

Served by the ALCF shared inference API (`openai/gpt-oss-120b`) — the same
endpoint and model id the frozen control was measured on. `harness gate-check`
clean on all six runs: 0 api_error, 0 unextracted.

| | seeds | mean | range | model calls |
|---|---|---|---|---|
| open-loop (framing A, k=31) | 12 / 8 / 12 | 10.7/30 | 8–12 | 960–990 |
| **framing L** | **18 / 16 / 18** | **17.3/30** | **16–18** | **571–616** |

**The ranges do not overlap: the worst framing-L seed beats the best open-loop
seed.** That claim needs no pairing choice and no significance test. Across all
nine (L seed, A seed) pairings the delta is +4 to +10, mean +6.7, with one loss
total (spec 181, in two pairings).

The loop wins while spending **~60% of the control's model calls**, because a
solved spec stops.

### Two confounds killed, not assumed away

1. **Endpoint drift.** The frozen 12/30 was measured months earlier. Re-running
   the open-loop control on the same warm endpoint at a matched 32-call budget
   reproduced it exactly (12/30). Per-sample SANY and median latency are flat
   across the whole session (16.6% / 22.9% / 23.9% / 25.7% / 15.2%; 20.3s /
   23.0 / 22.6 / 22.7 / 20.2), so the control's 8/30 third seed is spec-level
   sampling noise, not a degrading serve.
2. **Single-seed accident.** Seed 2 alone would have reported NULL (+4,
   p = 0.125). Reporting seed 1 alone (+6, p = 0.031) would have been exactly the
   sampling accident `W4DG_GATE2_SESSION_2026-07-29.md` warns about.

### What the per-spec view takes back

Only **two** specs — 13 and 15 — are solved by the loop in every seed and by
open-loop in none. 132 and 191 are 2/3; 32, 106, 133, 174 are 1/3. No spec is
ever open-loop-only.

So the defensible claim is **not** "the loop solves these six specs". It is: the
loop reliably adds about five to seven specs, the direction never reverses, but
*which* specs it adds varies by seed. That is a larger reachable set, not a
deterministic gain.

### Mechanism: the feedback, not the extra sampling

In seed 1, 5 of the 6 gained specs were won on a repair round rather than a fresh
generation (3 entered as `sany`, 2 as `tlc_error`). Across all 18 solves in that
seed, 9 came from the first round of 8 independent draws and 9 came from repair
rounds.

### A per-sample metric that must not be quoted as a comparison

Framing L stops a spec on its first pass, so an easy spec contributes one passing
row while open-loop banks 20+ on the same spec. Per-sample **pass** rate is
therefore structurally biased against L (3.0% vs 7.5%) and is not a capability
comparison. Per-sample **SANY** is biased the same direction, which makes L's
advantage there conservative: **24.1% [22.2, 26.1] vs 14.1% [12.8, 15.3]**,
pooled over 1,760 and 2,910 rows.

### The headline this licenses

An **untuned base model in the loop** (17.3/30 mean) beats the program's best
fine-tune measured open-loop (`gate2-w4dgm-120b-A`, 15/30) — and that fine-tune is
itself not distinguishable from its own base control (+3, p = 0.45).

Not yet run: **ARM L-tuned**, queued behind a Sophia serve. Until it lands,
nothing here licenses a claim about what tuning adds *on top of* the loop.

## Run commands

```
python3 tools/smoke/serve_preflight.py --model <served-id> --max-tokens 16384
python3 -m harness loop-eval --model openai:<served-id> --run-id loop-<arm> --chains 8 --rounds 4
python3 -m harness gate-check results/runs/loop-<arm>
```

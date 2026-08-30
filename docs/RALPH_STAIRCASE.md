# Ralph loop: the staircase to 30/30

Started 2026-08-30, Eric-directed. Loop owner: the Claude session. This file is
the loop's working memory: state, roadblocks, and the decision ledger. Update it
every iteration. PLAN.md stays immutable; this file does not amend it.

## Goal (ordered, each rung on the frozen 30-spec holdout)

1. **100% SANY**: every holdout spec gets at least one SANY-passing candidate
   from the best honest system configuration.
2. **100% TLC (Gold)**: every TLC-graded spec gets a TLC-accepting candidate.
3. **100% Diamond**: every such candidate is non-vacuous (Rule-5 clean) and
   mutation-sensitive.

"System" means any honest configuration measured by the frozen harness: framing
L loop, grammar-constrained decoding, repair prompts, model choice. Weights may
change only with clean data (dataset-audit-2026-08-29). No redefinition of
"pass", no holdout edits, Rule-9 audit on every counted pass.

## Budget

Eric authorized up to **75% of the weekly usage allocation** (his /usage is
authoritative; he watches it). Proxy guard for the loop:
`python3 /Users/eric/.claude/skills/orchestrator/estimate-usage.py --days 7`
— STOP the loop and ping Eric when trailing-7-day weighted_mtok exceeds
**2600** (assumption: ~1.5x the 2026-08-29 heavy-week reading of 1729; Eric can
correct this number here). Also stop on: goal reached, or a roadblock only Eric
can clear (OTP, spend, outward-facing action) — ping Discord per
notify-eric-discord-otp and keep working on whatever does not block.

## Current state (2026-08-30, iteration 0)

- Best measured system: framing-L loop on UNTUNED base 120b, 17.3/30 mean
  (18/16/18). Tuned loop 12/30 (1 seed), tuned open 16/30 (1 seed).
- Tuned 2x2 seeds + grammar arm A5 queued: job 177470 (Sophia, still Q),
  runner tools/run_tuned_2x2_seeds.sh with reconnect logic, monitor armed.
- Failure taxonomy (3,836 SANY failures, 6 arms): 51% parse, 34% unknown
  operator (of which 1,990 invented operators, 1,195 qualified-vs-unqualified
  INSTANCE). Grammar tla_module_v1.ebnf: 0/438 false rejects, 86.7% offline
  catch rate — not yet measured in-loop (A5 does that).
- Never-solved specs across every arm (candidates from reachability data):
  13, 14, 55, 106, 121, 128, 132, 133, 135, 141, 148, 158 (verify against
  pooled ledgers in iteration 1).
- Holdout facts that bound the ceiling: 86 and 183 are byte-identical (the
  TLAPS module); 105 is a 428-byte stub; 4 library specs are SANY-only; 2
  proof modules are TLAPS-graded. So "30/30 TLC" is really 24/24 TLC-graded.
- RL staircase design exists (docs/designs/2026-08-12-sany-tlc-grpo.md) with
  the vacuous-pass rung amendment proposed (tier 2.5 at 0.85) — an option,
  not a commitment; the loop measures cheaper levers first.

## Iteration protocol

1. Integrate any finished arms (monitor events, gate-check, never
   summary.json).
2. Rebuild the per-spec staircase from ALL ledgers: for each holdout spec,
   deepest rung reached (SANY / TLC / vacuity-clean / diamond) and by which
   system. The gap list drives everything.
3. Pick the single highest-leverage intervention for the shallowest rung with
   gaps. Prefer measurements over training. Candidates, in rough order:
   grammar in the loop (A5 result), repair-prompt fixes for the
   unknown-operator classes, INSTANCE-qualification rewriting, per-spec
   autopsies of never-solved specs, chains/rounds budget shape, TLC-feedback
   verbatim quality in framing L.
4. Implement, run against the live serve (through the runner's ensure_serve
   pattern), score with gate-check, record here.
5. Usage check (guard above). Commit. Next iteration.

## Decision ledger

- 2026-08-30 it0: loop created. Waiting on job 177470 for the serve; grammar
  arm A5 is the first planned measurement.
- 2026-08-30 it1: built tools/staircase.py (all-ledger, per-spec deepest rung).
  **Generation-only (framing A/L) union frontier is 5 specs:** 55, 121, 141,
  148 stuck at sany-passes-but-TLC-never-accepts; 135 at tlc_vacuous. Rung-1
  (at least one SANY pass ever) is ALREADY 30/30 — "100% SANY" at union level
  is met; the per-sample rate is what starves the upper rungs. Pooled over
  framings including B-repair, 29/30 have passed (135 the lone holdout).
  Autopsies: 55 (MCEcho) and 135/141 (MCReachable/Reachable pair) have
  COMPLETE prompts post-signature-fix (checked build_generation_prompt
  output: N1/I1/R1 and LimitedSeq/ConnectedToSomeButNotAll all demanded);
  their TLC-error rows are pre-fix history. 135/141 candidates that reach TLC
  die "Invariant violated by the initial state" — the loop DOES feed the
  trace back (diagnose -> tlc_violation -> truncate_trace), but only 4-6 rows
  per ~480 ever get that far. 148 (Nano, 491 lines) is 425/480 sany=fail.
  121 runs on a MED-confidence draft cfg whose own comments say the finite
  bound really needs the spec-122 MC wrapper — feasibility question, one
  deeper autopsy owed before spending serve budget on it.
  **Conclusion: per-sample SANY yield is the shared bottleneck for all 5;
  the queued grammar arm (A5) is the highest-leverage pending measurement.**
  Usage guard: 1641.6 wMtok / 2600 — ok.

## Roadblocks

- Job 177470 has sat in Q since 2026-08-29 ("No available resources"). The
  runner rides it out; if it is still Q at next iteration, consider the
  Sophia debug queue or a shorter walltime request as alternates.

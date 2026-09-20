# Prover milestones

These operational milestones implement Eric's requested SANY → TLC →
non-vacuity progression. They do not amend PLAN.md, replace its G1/G2 gates,
reduce populations, or authorize new resources. The final objective remains
corpus closure AND demonstrated proving on unseen specifications.

## Fixed acceptance rules

Binding immediate objective (2026-09-06): diagnose and correct the end-to-end
full-module generation failure, then demonstrate usable complete-module
generation before scaling training further. The eventual acceptance ladder
below remains unchanged. The frozen TRAIN20 diagnostic must account for every
case and distinguish time/token exhaustion, EOS/template/token-prefix mismatch,
extraction/module assembly, dependency/runtime errors, actual SANY errors, and
learning failure. Unknowns remain separate. Check known-good references through
the same extraction/checking path and exact training/inference token prefixes.
Use TRAIN-only evidence for debugging, never protected answers.

Completion requires an evidence-backed root-cause report and bounded matched
before/after correction on the frozen probe, followed by a predeclared
source-family-separated full-module development evaluation. A nonzero
reproducible complete-module baseline is required before broader scaling;
measured development gains and proof retention are required before promotion.
If the probe fails, test the simplest implicated component, not another broad
training run. Do not presume that more data or updates is the remedy.

The milestone order is binding: SANY first, TLC second, non-vacuous intended
behavior third. A later candidate must retain all earlier applicable checks on
that same checkpoint; successes from separate models do not compose. Supporting
proof-training experiments may continue, but cannot be reported as promotion
past an unmet milestone. The existing active prover goal remains the parent
objective, with these milestones as its acceptance ladder.

Before each measurement, freeze the model/checkpoint, task population and shape,
prompts, sampling/repair budget, verifier runtime and intended properties.
Keep every requested attempt in the accounting, including unattempted cases,
timeouts and infrastructure errors. Report those separately; they do not pass.
Never accumulate successes until a desired percentage is reached.

“100%” means every requested output in that frozen evaluation passed. It is not
a universal guarantee. Repeated samples of seven holes remain seven holes, not
one thousand different specifications. Scores from different checkpoints,
seeds, search systems or populations must not be combined into a model score.

## Milestones and evidence

| Milestone | Acceptance evidence | Does not establish |
|---|---|---|
| 1. 100% SANY | Every requested output completes and its module passes parsing and semantic analysis. Record generation and repair separately; incomplete outputs cannot satisfy this milestone. | Correct behavior, non-vacuity or proofs. |
| 2. 100% TLC acceptance | Every applicable state-machine task completes the fixed model check with unchanged intended properties/configuration. Follow PLAN's named expected-violation criterion where applicable. | Non-vacuous correctness or general theorem proving. |
| 3. 100% non-vacuous, intended-property correctness | Every counted behavioral pass additionally satisfies the applicable reachability, trap/mutation and semantic-audit checks. Type-only checks remain partial evidence. | Unbounded proof or transfer to unseen specifications. |
| 4. Required TLAPS proofs and unseen-task gains | All required proof-module obligations verify; the trained model/search system meets the unchanged decontaminated benchmark and baseline requirements in PLAN. | Completion of G1/G2 unless every other binding requirement is also met. |

G1 accounting retains all206 corpus entries. Pure libraries and proof modules
use the population-appropriate criteria in PLAN Amendment1, not a fabricated
TLC pass. The official holdout30, proof benchmark119 and recovered original18
retain their existing exclusions and reporting contracts. Additional diagnostic
sets never replace these gates.

Training can progress through syntax and model-checker objectives before the
later milestones are attained. Such intermediate rewards/results are explicitly
partial: vacuous passes, deleted behavior or weakened properties cannot become
terminal success. Verifier-derived rewards are RL with verifiable rewards.
AI-judge feedback is RLAIF and may supplement specification-intent review, but
does not replace real SANY/TLC/TLAPS results or the required semantic audit.

For Eric's requested reliability expansion, predeclare up to 1,000 attempts or
the authorized one-hour debug-job budget, whichever is reached first. Preserve
the requested denominator and report the achieved coverage if the clock wins;
do not label a partial run 1,000/1,000. Establish full-module capability separately
from token-hole repair. The 100% non-vacuity target needs executable checks as
well as any AI-judge feedback; a judge's approval alone cannot certify it.

## Evidence snapshot, 2026-09-05

- Latest paired syntax pilot:996/1000 SANY passes, four failures; only seven
  one-token repair prompts on two known modules,12 distinct candidates.
  Source: `results/runs/sany-paired-child-20260905/summary.json`.
  This is not100% and is not full-spec generalization.
- TLC pilot:7/7 fixed greedy curriculum checks passed; type-only checks retain
  partial status. This is a different checkpoint/task contract from the syntax
  pilot and the Llama proof experiments. Source: `docs/TLC-RL-2026-09-05.md`,
  with underlying `results/runs/online-tlc-rl-20260905-181617/` artifacts.
- Proof-training checkpoint:25/32 TRAIN tasks verified,0/4 reused DEV tasks.
  Source: `results/runs/proof-cuda-exposure-child-verified-20260905-v1/`.
  Better training fit is not demonstrated generalization.
- Prospective fresh14 evaluation:all28 human-reference/FALSE controls passed;
  matched evaluation7594766 completed. The original and post-hoc exact-fence
  replay both certify BASE0/14 versus checkpoint1/14 (MinNat only). Replay
  conservatively records one internal checker error per arm; independent SANY
  diagnostics reject those two candidates for temporal-level errors while both
  reference modules pass. No protocol target was proved. Sources:
  `results/runs/proof-fresh14-extraction-replay-20260905-v1/` and
  `results/runs/proof-fresh14-assertion-sany-20260905-v1/`.

Current job state and next actions belong in `docs/PROVER-GOAL-2026-09-05.md`;
inspect live state before relying on this dated snapshot. No milestone or final
gate is marked complete by this document.

## Priority reaffirmed, 2026-09-06

First unmet milestone: **1, full-module SANY reliability**. The recorded
996/1000 token-hole pilot is a diagnostic, not completion of this goal.
Before claiming progress to milestone 2, record the fixed full-module task
population and complete SANY acceptance result. Stage 3 combines executable
non-vacuity checks with intended-behavior review; RLAIF is a training signal,
not a substitute for those acceptance checks. No new acceptance result is
claimed by this priority update.

## Latest measured status, 2026-09-06

The ordered milestones above remain subgoals of the active native prover goal;
none is complete. On the matched 30-task, 45-second full-module evaluation,
both parent and child achieved 0/30 verified SANY passes. Parent accounting is
0 passed / 6 rejected / 24 unknown; child is 0 / 13 / 17. This is the current
full-module diagnostic, not a replacement for the final acceptance population.
See `results/runs/proof-fullmodule-learning-verified-20260906-v1/`.

The independent retention audit also confirmed regression on the separate
40-task proof-generation set: SANY 40/40 to 38/40, verified proofs 33/40 to
32/40. The experimental child is not promoted. These proof-hole results must
not be substituted for full-module generation. See
`results/runs/proof-fullmodule-retention-verified-20260906-v2/`.

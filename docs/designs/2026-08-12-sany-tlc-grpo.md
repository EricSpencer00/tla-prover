# Design: SANY→TLC staircase GRPO — restarting RL on measured reward variance

Status: proposed, pre-registered below. Written 2026-08-12 in answer to "we dropped
RL because it didn't converge; do we pick it up again now that we have gpt-oss-120b
and Argonne compute?"

## The answer, measured rather than argued

Yes — but the enabling change is **not** the bigger model or the bigger cluster. It
is that we now have a checkpoint whose samples disagree with each other, plus a
reward with a populated middle rung.

GRPO produces a gradient only when a sampled group scores non-uniformly. The RL era
died at `frac_reward_zero_std` of 72–78% (full-spec 78%, repair R1 73%, R2 72%). That
statistic is estimable today from ledgers already on disk: each Gate-2 arm has 32
draws per spec, so we can resample groups of size G and count how often the group is
uniform. No compute, no serve.

Fraction of groups with **zero** reward variance (4,000 resamples per cell, seed 0):

| arm | G=4 | G=8 | G=16 |
|---|---|---|---|
| untuned base, binary pass/fail | 81.2% | 73.7% | 67.6% |
| untuned base, SANY→TLC staircase | 73.8% | 64.4% | 53.8% |
| W4DG post-fix, binary pass/fail | 67.9% | 58.9% | 52.7% |
| **W4DG post-fix, SANY→TLC staircase** | **38.2%** | **22.8%** | **13.9%** |
| W4DG-genprompt, SANY→TLC staircase | 45.1% | 27.9% | 16.8% |

The untuned base under a binary reward sits at 73.7% at G=8 — inside the 72–78% band
that killed every historical run. That agreement is what makes the rest of the table
credible: the method reproduces the known failure before predicting a new success.

**W4DG post-fix under the staircase at G=8 is 22.8%, so 77% of groups carry a
gradient.** Both changes are load-bearing and neither suffices alone: base+staircase
is 64.4%, W4DG+binary is 58.9%, only the combination reaches 22.8%.

Why: the tier histogram moved.

| arm | no module | SANY fail | TLC rejects | pass |
|---|---|---|---|---|
| untuned base | 0.1% | 89.5% | 3.5% | 6.9% |
| W4DG post-fix | 0.1% | 69.1% | **17.2%** | 13.6% |

The historical rewards were effectively binary because 89.5% of draws landed in one
bucket. The middle rung — parses, TLC ran and rejected it — grew from 3.5% to 17.2%,
and that is where within-group disagreement now comes from.

## Reward

Four tiers, computed by the existing frozen verifier path (`runner.eval_module_text`
→ `repair.verdict_of`), no new scoring code:

| tier | condition | reward |
|---|---|---|
| 0 | no module extracted, or api_error | 0.00 |
| 1 | module emitted, SANY fails | 0.25 |
| 2 | SANY passes, TLC runs and rejects | 0.60 |
| 3 | SANY passes, TLC accepts, `tlc_vacuity == "clean"` | 1.00 |

Tier 3 requires the Rule-5 vacuity gate that already exists in `verdict_of:559`. A
vacuous TLC pass scores **tier 2, not tier 3** — the model cannot climb by emitting a
spec whose invariant is trivially true.

Population-awareness is inherited: for LIBRARIES specs SANY alone is the criterion
(tier 3 at SANY pass), and PROOF_MODULES are excluded from the RL prompt pool
entirely rather than scored on TLAPS.

## Why the reward is affordable

Verification is not the bottleneck. Measured `budget_used` on a Gate-2 row:
`sany_s 0.2, tlc_s 0.2, model_s 86.7`. Verification is ~0.4s against ~87s of
generation, so the reward costs under 1% of rollout wall time. A 500-step run at
G=8 is 4,000 generations; at the concurrency-16 rate observed in Gate-2 (~7.5s per
sample effective) that is roughly 8h of rollout — one job.

## Prompt pool

Framing-A generation prompts (`gen_eval.build_generation_prompt`, shape P1) over the
**W4 survivor corpus**, never the holdout. Two reasons P1 rather than the SFT shapes:
it is the shape Gate-2 scores, and it is the one shape no corpus has ever trained on,
so an RL gain there is not re-teaching something SFT already covered.

Decontamination is by module name and `seed_key` against `corpus/holdout_30.json`,
asserted at load time and again at first step. **This is the defect that invalidated
the RL era's published number** — `fullspec_dataset.py` defaulted `include_topics=True`
with no holdout filter, so all 30 holdout tasks were in the GRPO prompt pool. The
loader for this arm fails closed: it aborts if any holdout module name appears.

## Configuration

- **Policy:** LoRA over gpt-oss-120b bf16, identical geometry to the SFT arms
  (r=8, α=16, q/k/v/o + `target_parameters` on the experts, 536,813,568 trainable).
- **Reference model:** the base with the adapter disabled (PEFT), so no second
  120b copy is materialized. This is the memory-feasibility crux — see risks.
- **Start checkpoint:** the best SFT arm at the time of launch. Today that is
  W4DG post-fix; if the mech arm (Amendment 24) beats it on per-sample rate, start
  from mech instead and re-run the variance table first.
- **G = 8**, temperature 1.0 for rollouts. G=16 halves zero-variance again (13.9%)
  and doubles rollout cost; G=8 is the starting point, G=16 is the fallback if
  measured `frac_reward_zero_std` exceeds the abort floor.
- **Steps:** 500, checkpoint every 50.

## Guardrails, each tied to a recorded failure

| guard | threshold | why |
|---|---|---|
| `frac_reward_zero_std` logged per step; **abort** if the running mean exceeds 0.55 over any 50-step window | 0.55 | the historical failure band was 0.72–0.78; 0.55 is well above the predicted 0.23 and well below the failure regime |
| entropy logged per step; **abort** below 0.15 | 0.15 | full-spec collapsed 0.44→0.32, repair ran at 0.003–0.1 |
| within-group byte-identical completion rate; **abort** above 0.5 | 0.5 | the July run emitted byte-identical completions within a group at temp 0.5 |
| vacuous share of tier-3 draws, logged | report only | reward-hacking canary; the vacuity gate should hold it near the 1.3–1.9% seen in SFT arms |
| holdout module names in the prompt pool | **fail closed at load** | the defect that invalidated the published 9/30 |

The first three abort the job rather than warn. The RL era's expense was not that
runs failed; it was that they ran 965 steps while failing.

## Pre-registration

**Primary endpoint:** per-sample pass rate on the frozen 30-spec holdout, framing A,
k=32, ledger-scored via `gate_check`, compared against the arm the RL run started
from — not against the untuned base. A GRPO arm that merely reproduces its own SFT
starting point is a null result.

**Secondary:** SANY pass rate and the tier histogram, reported whatever they show.
The mechanism claim is that RL moves mass from tier 1 to tiers 2–3; the tier
histogram tests that directly and can falsify the mechanism even if the primary
endpoint moves.

**Reported regardless of outcome**, both framings, with the two-level paired bootstrap
on byte-identical prompts.

**What would falsify the premise:** measured `frac_reward_zero_std` in the first 50
steps landing above 0.55 despite the 0.23 prediction. That would mean the offline
resampling estimate does not transfer to on-policy rollouts at temperature 1.0 —
which is the single assumption this design rests on and cannot verify offline.

## Risks

1. **Memory feasibility is unproven, and it is the real blocker.** The SFT runs fit
   218GB of bf16 weights across 8×A100-40GB with FSDP activation checkpointing and
   parameter offload. GRPO adds rollout generation to the same allocation. Colocated
   vLLM will not fit alongside an offloaded FSDP policy. Mitigation: run generation
   against a **separate serve job** over the existing tunnel (the harness already
   talks to an OpenAI-compatible endpoint) and keep the training job weights-only.
   That decouples the two memory budgets at the cost of a checkpoint-reload cadence —
   the policy served for rollouts lags the trained policy by one checkpoint interval,
   making this closer to iterative rejection-sampling-with-partial-credit than to
   strict on-policy GRPO. **This is a real design compromise and should be named as
   such in the amendment, not glossed.**
2. **The offline variance estimate is measured at temperature 0.8** (the Gate-2
   sampling temperature) and rollouts would run at 1.0. Higher temperature should
   raise diversity and therefore lower zero-variance, so the estimate is likely
   conservative — but it is an extrapolation.
3. **Tier 2 may be a trap.** Rewarding "parses but TLC rejects" at 0.60 could teach
   the model to emit parseable specs that are semantically empty. The vacuity gate
   blocks the tier-3 version of this; the tier-2 version is only blocked by the
   0.40 gap to tier 3. Watch the tier histogram for tier-2 mass growing while tier-3
   stalls.

## Cost

One 500-step run: ~8h rollout + training on one node, plus a serve node for
generation. Gate-2 eval afterward is the standard ~4h both framings. Total roughly
one day of one node pair, against a reserved-run budget that has been spent on
single SFT arms of comparable size.

## Sequencing

This is gated on the mech arm reading out (Amendment 24, in flight). If mech beats
W4DG post-fix, the variance table is recomputed from the mech ledger and the run
starts from that checkpoint instead. If mech regresses, W4DG post-fix remains the
start and this design is unchanged.

Independent of that: grammar-constrained decoding is a cheaper attack on the same
tier-1 mass (69.1% SANY failures) and needs no training compute at all. If grammar
decoding collapses tier 1, the variance table must be recomputed before this run —
a checkpoint that always parses has *less* tier-1/tier-2 disagreement, and could push
zero-variance back up. The two interventions are not additive and the order matters.

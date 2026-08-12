# Fine-tuning strategy for a verified TLA+ prover: measured position and options

Prepared 2026-08-12 for the fine-tuning strategy discussion. All numbers are from
ledger re-scores of `rows.jsonl` on the frozen 30-spec holdout unless stated
otherwise. A composition arm is training on Argonne as this is written; its result
is not included and is not predicted here.

## Summary

Six supervised fine-tunes and seven RL runs have been measured. One arm beats the
untuned base: W4-diamond-gold, at 13.5% per-sample against 6.9% (+0.086, p=0.063,
paired bootstrap on byte-identical prompts). Every RL run failed for the same
mechanical reason, and that reason is the same fact that limits the SFT arms:
between 68% and 74% of failed samples do not parse, against 2.1% that model the
system incorrectly. The corpus contains no instance of that failure mode.

## Corrections to the agenda's stated position

Four points in the supplementary material are out of date or not supported by the
primary evidence. Raising them first because they change what the meeting should
decide.

**`chattla-v2-sft2` is not the most recent or the best model.** It is the arm that
failed Gate-2: framing A flat at 11/30 against base 12/30, framing B a real
regression (pass@1 6/23 against baseline 15/23). Three arms have been trained since.
The best measured checkpoint is `chattla-w4dg-120b` (W4-diamond-gold), which is the
only fine-tune to beat base on per-sample yield.

**The published 30% Gold / 9-of-30 result has three defects.** Verified directly
against the repo and logs: (1) all 30 holdout module names appear in the GRPO topic
pool `diamond_gen_topics.json`, and the RL dataset loader implements no holdout
filter, so the models received TLC-verifier reward on the descriptions of the exact
30 evaluation tasks; the SFT path does filter, so this is specific to the RL
loaders; (2) the eval is a four-shot repair loop with verifier feedback, and
cross-tabulating result against `attempts_used` gives a single-shot rate of 3/30;
(3) the LoRA merge failed with an argument error five seconds before the eval that
names the merged Ollama tag, so the evaluated checkpoint cannot be confirmed as the
GRPO-trained weights. This number should not be carried into new work without those
three qualifiers.

**"RL into higher pass rates" has already been attempted seven times.** All failed,
and the failure is diagnosed rather than suspected. Detail in the RL section below.
The short version: GRPO needs reward variance within a sampled group, and when
nearly every completion fails to parse, every completion in the group scores
identically and the gradient is zero. RL is blocked behind parse competence, not
behind reward design; three reward designs were tried and all three starved.

**`tla-w4-diamond-gold` does contain commented code**, though sparsely: 38.7% of
targets contain at least one comment, with a median of 7 comment lines in those
targets, and an overall comment-line density of 3.9% against a median target length
of 75 lines. The concern behind the claim is reasonable — comment density is low,
and there is no supervision teaching the model to explain its own specs — but "lacks
any commented code" overstates it.

The vacuity and reward-hacking concern is better founded and quantified below.

## Measured arms

Framing A, k=32, 30-spec frozen holdout. Per-sample rate is the primary statistic;
pass@32 is reported second because it discards roughly 97% of the evidence and has
twice produced misleading conclusions in this program.

| arm | corpus | per-sample | pass@32 | vs base |
|---|---|---|---|---|
| untuned gpt-oss-120b | — | 6.9% (66/960) | 12/30 | — |
| v2 SFT | 260 harmony pairs | 4.9% (47/963) | 11/30 | worse |
| W4-diamond-gold | 3,534 rows, bare rendering | **13.5% (130/960)** | 16/30 | **+0.086, p=0.063** |
| W4DG-genprompt | 4,219 rows, prompt-aligned | 7.7% (69/896) | 12/30 | −0.018, p=0.66 |
| mech (composition) | 6,906 rows incl. repair | training | — | pending |

Framing B (repair from a corrupted spec) per-sample: untuned baseline 55.0%,
v2 SFT 28.7%, W4DG-genprompt 20.5%. Every fine-tune so far has *degraded* repair
performance relative to the untuned model, which is the strongest single argument
that the corpus composition, not the volume, is what needs to change.

External reference points from the same audit: Opus 4.7 zero-shot reaches 7/30
(23.3%) non-vacuous on the FormaLLM validation set, and the best untuned model in a
30-model sweep reached 8.6% semantic pass on 205 specs. Frontier prompting is
currently ahead of every fine-tune we have produced.

## Two negative results

**Prompt alignment.** W4DG-genprompt tested the hypothesis that training pairs
should use the same prompt the specs were verified under. It regressed to base
(13.5% → 7.7%) and raised `sany=fail` from 68.1% to 74.1%. The candidate mechanism,
untested, is that training on one rigid template binds the capability to that
template while Gate-2 uses a third prompt shape. The practical lesson is that
rendering choices are not cosmetic and can erase a real gain.

**Parse recovery is not pass recovery.** A deterministic lint pass (drop
builtin-colliding declarations, add missing `EXTENDS`, dedupe definitions) made 88
of 454 failed candidates parse across 9 unsolved specs, and flipped zero specs to
passing. Making output parse is necessary and demonstrably not sufficient.

## The RL era, and why it stopped

Seven runs on gpt-oss-20b, 2026-03 to 2026-04, on two 49GB RTX 8000s.

| run | method | outcome |
|---|---|---|
| per-action | GRPO | no surviving artifacts; flat reward reported second-hand |
| piecewise | DPO | final loss 0.6661 against ln 2 = 0.6931, accuracy 0.60 |
| full-spec | GRPO | 172 steps, mean reward 0.0511, 37 of 172 steps nonzero |
| repair R1 | GRPO | 965 steps, mean reward 0.1487, 703 steps at zero variance |
| repair R2 | GRPO | 600 steps, mean 0.0930, 430 at zero variance |
| repair R3 | — | aborted pre-training: 152 usable pairs against a floor of 300 |
| repair (July) | GRPO | 89 steps at uniform zero reward; after a fix, 1 of 7 rows improved |

`frac_reward_zero_std` equals 1 on the majority of steps in every GRPO run. Repair
R1's mean reward of 0.1487 is the shaping function's hard-coded "no change" constant
of 0.15, so the run sat on the flat part of its own reward for 965 steps. KL stayed
between 0.002 and 0.014, so this was not policy collapse under KL. There is no
evidence of reward hacking and none of verifier false positives.

The consequence for strategy: **reward variance is a function of parse rate.** RL
becomes viable at the point where a meaningful fraction of a sampled group parses,
and not before. Sequencing RL after mechanics competence is not a preference, it is
a precondition.

## What "100%" can mean

The program's locked north-star is guaranteed-correct TLA+ obtained through the
verification loop, not through the weights. That distinction should be explicit in
the meeting, because it determines which metric the fine-tuning strategy optimizes.

A model that emits correct TLA+ 100% of the time on the first try is not a realistic
target and is not needed. What the loop needs is a low expected number of iterations
to a verified spec. Framed that way:

- 100% correctness is supplied by the verifier, which is sound and already in place.
- The weights' job is to reduce iterations and to keep the loop from stalling. A
  spec that never parses cannot be repaired productively, which is the observed
  stall mode.
- The right headline metric is therefore expected-iterations-to-verified, or
  equivalently the pass@k curve's shape, not single-shot pass rate. We do not
  currently report this, and adopting it would change which arms look good. It is
  worth deciding at the meeting whether to adopt it.

## Dataset assessment: `tla-w4-diamond-gold`

Composition of the 4,119-row cut: `mutex_locks` 35.5%, other 18.0%, consensus 15.8%,
commit protocols 8.9%, queues and buffers 8.9%. Liveness rows are 12.4% of the
render against a public TLA+ liveness rate of 23–34%.

The vacuity and reward-hacking concern raised in the agenda is supported: the real
mutation-catch rate is 12.7%, meaning most specs in the corpus do not have
invariants strong enough to detect a single-operator mutation. A spec that passes
TLC with a weak invariant is a verified spec that teaches little. The mutation-gated
"diamond" tier exists to address this and is the tier that measured best in the
TLA-Prover ablation, which is consistent with the concern being real.

Scenario diversity, by contrast, was probably never the bottleneck: W4-diamond-gold
varied noun, scenario and number combinatorics heavily, and the failure profile
barely moved. The evidence points at what the corpus *demonstrates* (only
already-correct specs) rather than at how many distinct scenarios it covers.

## Options, with predicted effect

Ordered by evidence strength, not by appeal. Each is a single knob; the program's
worst results came from turning several at once.

**1. Mechanics supervision — in flight.** Add verified broken-to-fixed pairs so the
corpus contains the dominant failure mode. 2,787 pairs were manufactured from the
existing survivor corpus by corrupting a spec, confirming with SANY and TLC that the
corruption really fails, and using the original text as the repair target. No
teacher model, no rejection sampling, minimal-by-construction fixes. Result expected
within a day. This is the direct attack on the 68–74%.

**2. Grammar-constrained decoding — untested, no training cost.** If parse failure is
mechanical, constraining generation to the TLA+ grammar attacks it without a training
run at all. Two EBNF grammars are already scaffolded in the harness
(`tla_module_v0.ebnf`, `tla_proof_v0.ebnf`). This is attractive precisely because it
is orthogonal to the training arms and cannot confound them. It is the cheapest
untried lever in the program.

**3. Multi-task environment split — untested.** The strongest positive result in the
Meta FAIR synthetic-data work is that splitting a fixed budget across four task
environments beats concentrating it on one, on both pass@10 and out-of-distribution
generalization. We train one shape at a time and already own verifiers for four:
generation, repair, abduction (counterexample trace to violated invariant), and
fuzzing (the mutation battery inverted). Amendment 16 treated task-shape mismatch as
a confound to eliminate; this evidence says it may be a lever to use.

**4. RL, after (1) or (2) lands.** Improvement-reward GRPO on repair is the natural
fit, and the existing implementation is reusable. It should not be restarted until a
sampled group produces score variance; the honest test is to measure
`frac_reward_zero_std` on a candidate checkpoint before committing compute.

**5. More data of the current kind — weakest.** Going from 260 to 4,119 rows roughly
doubled per-sample yield but left the failure profile unchanged. Volume has visible
diminishing returns against a corpus that omits the failure mode.

## Method and infrastructure notes

Eleven defects have been found and fixed across the training and measurement paths;
four of the six training defects exited 0 on runs that had not trained what they were
supposed to train. The two that matter for anyone reading old results: a
gpt-oss-specific LoRA selector left a dense model's FFN frozen at 0.0195% trainable
while reporting success, and a prompt-construction bug under-specified 13 of 30
framing-A prompts, corrupting every framing-A measurement recorded before
2026-07-29. Numbers from before those fixes should not be compared against numbers
from after them.

Current guards: an aborting trainable-parameter floor, attach-time expert-coverage
reporting, exit-code propagation through PBS, a mandatory preflight against real
weights, ledger-only scoring, and derived-seed decode provenance.

## Questions for the meeting

1. Do we adopt expected-iterations-to-verified as the headline metric, in place of
   single-shot pass rate?
2. Is grammar-constrained decoding worth doing before more fine-tuning, given it
   needs no training compute and cannot confound the training arms?
3. Should the next corpus investment go to task-shape diversity (four environments)
   or to depth in generation and repair alone?
4. The 30-spec holdout is the binding constraint on statistical power: effects below
   roughly 4 points cannot be resolved. Widening it requires an amendment and a
   decontamination pass. Do we spend that?
5. What is published, and with which qualifiers, given the three defects under the
   existing 30% result?

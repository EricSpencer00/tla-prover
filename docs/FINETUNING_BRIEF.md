# Fine-tuning a verified TLA+ prover: measured position, history, and options

Prepared 2026-08-12 for the fine-tuning strategy discussion. Covers every training
run in the program: the DPO and GRPO era of 2026-03/04 in `LUC-AI4FM/TLA-Prove`, and
the supervised fine-tuning era of 2026-07/08 in `prove-TLA`. All numbers are ledger
re-scores of `rows.jsonl` on the frozen 30-spec holdout unless stated otherwise. A
composition arm is training on Argonne as this is written; its result is not included
and is not predicted here.

## Summary

Six supervised fine-tunes and seven RL runs have been measured. One arm beats the
untuned base: W4-diamond-gold, at 13.5% per-sample against 6.9% (+0.086, p=0.063,
paired bootstrap on byte-identical prompts). Every RL run failed for the same
mechanical reason, and that reason is the same fact that limits the SFT arms:
between 68% and 74% of failed samples do not parse, against 2.1% that model the
system incorrectly. The corpus contains no instance of that failure mode.

## Corrections to the circulated agenda

Four points in the supplementary material are out of date or not supported by the
primary evidence. Raising them first because they change what the meeting should
decide.

**`chattla-v2-sft2` is not the most recent or the best model.** It is the arm that
failed Gate-2: framing A flat at 11/30 against base 12/30, framing B a real
regression (pass@1 6/23 against baseline 15/23). Three arms have been trained since.
The best measured checkpoint is `chattla-w4dg-120b` (W4-diamond-gold), which is the
only fine-tune to beat base on per-sample yield.

**The published 30% Gold / 9-of-30 result has three defects**, each verified
directly against the repo and logs. Detail in the measurement-defects section; the
short form is that the holdout tasks were in the RL prompt pool, the eval is
four-shot with verifier feedback rather than single-shot, and the evaluated
checkpoint cannot be confirmed as the GRPO-trained weights.

**"RL into higher pass rates" has already been attempted seven times.** All failed,
and the failure is diagnosed rather than suspected. GRPO needs reward variance within
a sampled group, and when nearly every completion fails to parse, every completion in
the group scores identically and the gradient is zero. RL is blocked behind parse
competence, not behind reward design; three reward designs were tried and all three
starved.

**`tla-w4-diamond-gold` does contain commented code**, though sparsely: 38.7% of
targets contain at least one comment, with a median of 7 comment lines in those
targets, and an overall comment-line density of 3.9% against a median target length
of 75 lines. The concern behind the claim is reasonable, since comment density is low
and nothing in the corpus teaches the model to explain its own specs, but "lacks any
commented code" overstates it. The vacuity and reward-hacking concern is better
founded and is quantified in the dataset section.

## Method space

Three methods have been used across the two eras. PPO, ORPO, KTO and SimPO appear
nowhere. An earlier draft of this review stated that no RL method had been run; that
was wrong, because it searched prove-TLA, which holds the corpus and eval harness,
and not TLA-Prove, which holds the trainers. ROADMAP.md:47's reference to "our
existing repair-GRPO" is accurate.

## SFT era, 2026-07-12 to 2026-08-05

Framing A, k=32, 30-spec frozen holdout. Per-sample rate is the primary statistic;
pass@32 is reported second because it discards roughly 97% of the evidence and has
twice produced misleading conclusions in this program.

| run | corpus | base | result | comparison |
|---|---|---|---|---|
| v2_sft1 | 39 plain-text pairs | 20b | 0/10, 82% of samples unextractable | directional, k=3 |
| v2_sft2 | 260 harmony pairs | 20b | 2/30 pass@4 (first passes recorded) | directional |
| v2_sft2 | same | 120b | 4.9% (47/963), A 11/30 pass@32 | base 12/30 |
| W2.6 repair-v1 | 508 repair triples | 20b | B 9/23 pass@1, 9/23 pass@4 | base 8/23, 17/23 |
| W4-diamond-gold | 3,534 rows, bare rendering | 120b | **13.5% (130/960)**, 16/30 pass@32 | base 6.9% (66/960), 12/30 |
| W4DG-genprompt | 4,219 rows, prompt-aligned | 120b | 7.7% (69/896), 12/30 pass@32 | base 6.9%, 12/30 |
| mech (composition) | 6,906 rows incl. repair | 120b | training | pending |

Paired two-level bootstrap on byte-identical prompts (n=17 specs): W4-diamond-gold
vs base **+0.086, p=0.063**; W4DG-genprompt vs base −0.018, p=0.66.

A further arm, Qwen3.6-27B dense, is retracted rather than reported: a gpt-oss-specific
`target_parameters` selector matched nothing on a dense model, leaving the FFN frozen
at 0.0195% trainable while the job exited 0.

Framing B (repair from a corrupted spec) per-sample: untuned baseline 55.0%, v2 SFT
28.7%, W4DG-genprompt 20.5%. Every fine-tune so far has *degraded* repair performance
relative to the untuned model, which is the strongest single argument that corpus
composition, not volume, is what needs to change.

External reference points from the same audit: Opus 4.7 zero-shot reaches 7/30
(23.3%) non-vacuous on the FormaLLM validation set, and the best untuned model in a
30-model sweep reached 8.6% semantic pass on 205 specs. Frontier prompting is
currently ahead of every fine-tune we have produced.

### Two negative results

**Prompt alignment.** W4DG-genprompt tested the hypothesis that training pairs should
use the same prompt the specs were verified under. It regressed to base (13.5% →
7.7%) and raised `sany=fail` from 68.1% to 74.1%. The candidate mechanism, untested,
is that training on one rigid template binds the capability to that template while
Gate-2 uses a third prompt shape. The practical lesson is that rendering choices are
not cosmetic and can erase a real gain.

**Parse recovery is not pass recovery.** A deterministic lint pass (drop
builtin-colliding declarations, add missing `EXTENDS`, dedupe definitions) made 88 of
454 failed candidates parse across 9 unsolved specs, and flipped zero specs to
passing. Making output parse is necessary and demonstrably not sufficient.

## RL era, 2026-03-22 to 2026-04-15

Hardware was two 49GB RTX 8000s, which set the batch geometry throughout. All runs
are gpt-oss-20b. Training logs were untracked from the working tree in a later
cleanup and survive only in git history at `e79a250` and `511a492`.

| run | method | reward | outcome |
|---|---|---|---|
| per-action 20b | GRPO | tier staircase, gold 1.0 to bronze 0.1 | no log, checkpoint or eval found; flat reward reported second-hand |
| piecewise DPO | DPO | preference pairs on a VARIABLES→TypeOK→Init→Next curriculum | final loss 0.6661 against ln 2 = 0.6931, accuracy 0.60, margins 0.0599 |
| full-spec | GRPO | 7 weighted components, TLC full 0.35 | 172 steps, mean reward 0.0511, 37 of 172 steps nonzero, entropy 0.44→0.32 |
| repair R1 | GRPO | improvement (after − before), shaped | 965 steps, mean reward 0.1487; 703 of 965 steps at zero reward variance |
| repair R2 | GRPO | same | 600 steps, mean 0.0930, 430 of 600 zero-variance |
| repair R3 | — | — | aborted before training: 152 in-band pairs after dedup against a floor of 300 |
| repair, July, off-main | GRPO | improvement | 89 steps at uniform zero reward; after a reward-density fix, 1 of 7 held-out rows improved; reverted from main at `9724cef` |

DPO v13 is the one arm reported as a gain: 9/20 SANY and 5/20 TLC against v11's 6/20
and 2/20, from 17 preference pairs evaluated on 20 problems.

A separate `rl_loop` (generate, verify, augment, re-SFT; not a policy-gradient
method) ran 266 cycles over two weeks and left 228 benchmark CSVs. SANY pass rate
trended down over that span, roughly 80% to 65%; TLC rose from roughly 10% to 20–25%.
The projection recorded in `README_RL_SETUP.txt`, 85% SANY and 40–50% TLC after ~15
cycles, was not reached.

### Reward variance

`frac_reward_zero_std` equals 1 on the majority of logged steps in every GRPO run:
all completions in a group score identically, the advantage is zero, and the update
is zero. Repair R1's mean reward of 0.1487 is the shaping function's hard-coded "no
change" constant of 0.15, so the run sat on the flat part of its own reward for 965
steps. KL stayed between 0.002 and 0.014 throughout, so this was not a
policy-collapse-under-KL failure; it was reward starvation with entropy collapse
alongside (0.44 to 0.32 full-spec, 0.003 to 0.1 on repair). The July attempt records
the endpoint mechanically: at temperature 0.5 the model emitted byte-identical
completions within a group.

We found no evidence of reward hacking and none of verifier false positives. The
reward was not gamed; it was flat.

## Attribution

The three candidate causes are all present, in sequence, and they are separable.

**Training method was implicated once, in the RL era, for a reason that is diagnosed
rather than suspected.** GRPO requires reward variance within a sampled group, and on
this task at this model scale there was none: a group of four completions to a TLA+
generation prompt nearly always scores identically, because almost all of them fail
to parse. Three separate reward designs were tried against this (tier staircase,
seven-component partial credit, improvement-over-baseline) and the third was still
producing `frac_reward_zero_std = 1` on 73% of steps. The constraint is a property of
the reward landscape, not of any one implementation.

Nothing implicates the SFT objective. It has been varied only in its data.

**Data provenance was the binding constraint through run 3, and correcting it
produced the only positive result.** v2_sft2 and repair-v1 both collapsed sampling
diversity: repair-v1 added zero specs over greedy at k=4 while the baseline added
nine. Amendment 17 attributed this to training a model on rejection-sampled outputs
of its own family and made cross-family provenance the condition for resuming
fine-tuning. W4-diamond-gold, built from Claude-Opus teachers, is the only arm to
beat base. The mechanism was tested in the sense that repair-v1 removed the
task-shape confound and the collapse reproduced anyway.

**Configuration defects were the most expensive in elapsed time and the most
dangerous to interpretation**, because four of them exited 0. Defect 1 below produced
a written base-model comparison reporting that gpt-oss collapses entropy where
Qwen3.6 does not; it was retracted the same day it was committed (`4771fc4d`,
`eb111535`). The retraction was prompted by reading the trainable-parameter
percentage, which at that point nothing enforced. It is now a floor that aborts.

Data quality in the narrower sense (what the corpus teaches) is the open question
rather than an established cause. Between 68% and 74% of sampled failures are
`sany=fail`, meaning the emitted TLA+ does not parse, against 2.1% attributable to
modeling the system incorrectly. Every corpus target is a verified spec, so the
training data contains no instance of the failure mode that accounts for two-thirds
of the errors.

**The two eras failed against the same wall from opposite sides.** GRPO got no
gradient because a group of samples nearly always scored identically, and SFT's
failures are 68–74% `sany=fail`; both are the same fact, that most samples do not
parse. Under a policy-gradient objective an unparseable sample carries no learning
signal, which is what starved the reward. Under imitation it is absent from the data.
This is the argument for treating parse-level competence as the thing to supervise
directly, and it is also the precondition for RL becoming viable: reward variance
appears once a meaningful fraction of a sampled group parses.

The most recent result is unexplained. Aligning the SFT prompt to the contract each
survivor was verified under moved framing A from 13.5% to 7.7% per-sample. Gate-2
framing A uses a third prompt shape, so one candidate is template binding, but this
has not been tested. The difficulty probe measures pass rate under the training prompt
itself and would discriminate; it is 436 rows short of complete.

## What "100%" can mean

The program's locked north-star is guaranteed-correct TLA+ obtained through the
verification loop, not through the weights. That distinction should be explicit in
the meeting, because it determines which metric the fine-tuning strategy optimizes.

A model that emits correct TLA+ 100% of the time on the first try is not a realistic
target and is not needed. What the loop needs is a low expected number of iterations
to a verified spec. Framed that way:

- 100% correctness is supplied by the verifier, which is sound and already in place.
- The weights' job is to reduce iterations and to keep the loop from stalling. A spec
  that never parses cannot be repaired productively, which is the observed stall mode.
- The right headline metric is therefore expected-iterations-to-verified, or
  equivalently the shape of the pass@k curve, not single-shot pass rate. We do not
  currently report this, and adopting it would change which arms look good. It is
  worth deciding at the meeting whether to adopt it.

## Dataset assessment: `tla-w4-diamond-gold`

Composition of the 4,119-row cut: `mutex_locks` 35.5%, other 18.0%, consensus 15.8%,
commit protocols 8.9%, queues and buffers 8.9%. Liveness rows are 12.4% of the render
against a public TLA+ liveness rate of 23–34%.

The vacuity and reward-hacking concern raised in the agenda is supported: the real
mutation-catch rate is 12.7%, meaning most specs in the corpus do not have invariants
strong enough to detect a single-operator mutation. A spec that passes TLC with a weak
invariant is a verified spec that teaches little. The mutation-gated "diamond" tier
exists to address this and is the tier that measured best in the TLA-Prover ablation,
which is consistent with the concern being real.

Scenario diversity, by contrast, was probably never the bottleneck: W4-diamond-gold
varied noun, scenario and number combinatorics heavily, and the failure profile barely
moved. The evidence points at what the corpus *demonstrates* (only already-correct
specs) rather than at how many distinct scenarios it covers.

## Options, with predicted effect

Ordered by evidence strength, not by appeal. Each is a single knob; the program's
worst results came from turning several at once.

**1. Mechanics supervision — in flight.** Add verified broken-to-fixed pairs so the
corpus contains the dominant failure mode. 2,787 pairs were manufactured from the
existing survivor corpus by corrupting a spec, confirming with SANY and TLC that the
corruption really fails, and using the original text as the repair target. No teacher
model, no rejection sampling, minimal-by-construction fixes. Result expected within a
day. This is the direct attack on the 68–74%.

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
fuzzing (the mutation battery inverted). Amendment 16 treated task-shape mismatch as a
confound to eliminate; this evidence says it may be a lever to use.

**4. RL, after (1) or (2) lands.** Improvement-reward GRPO on repair is the natural
fit, and the existing implementation is reusable. It should not be restarted until a
sampled group produces score variance; the honest test is to measure
`frac_reward_zero_std` on a candidate checkpoint before committing compute.

**5. More data of the current kind — weakest.** Going from 260 to 4,119 rows roughly
doubled per-sample yield but left the failure profile unchanged. Volume has visible
diminishing returns against a corpus that omits the failure mode.

## Defects found and fixed

Eleven defects have been found across the training and measurement paths. They are
listed because they determine which historical numbers are comparable to which.

### Configuration

Six defects, four of which produced a clean exit code on a run that had not trained
what it was supposed to train.

1. `target_parameters` hardcoded for gpt-oss. Dense FFN frozen, 0.0195% trainable,
   exit 0. Invalidated the Qwen arm and, with it, the base-model comparison.
2. `is_moe()` read only the top-level config. Qwen3.5-35B-A3B, with 256 routed
   experts, resolved as dense. Nothing downstream catches this, because the dense path
   yields `all-linear`, which covers attention and the shared expert and clears the
   0.1% trainable floor on its own.
3. PBS scripts echoed `TRAIN_EXIT=$?` and then exited 0, so PBS recorded success for
   failed runs.
4. `Mxfp4Config(dequantize=True)` was passed for any gpt-oss model rather than for
   MXFP4 checkpoints. On the pre-dequantized bf16 export this marks the model quantized
   without dequantizing, and transformers 5.12.1 refuses to train it (job 170856, exit
   1 at 3m24s). The environment had drifted from the 5.6.2 the recipe was proven
   against.
5. A two-GPU `CUDA_VISIBLE_DEVICES` hardcode in train.py.
6. The Sophia staging tree carried stale copies of `lora_resolver.py` and `train.py`
   relative to the home tree.

Defects 1–3 and 5 are fixed with an aborting trainable-parameter floor and attach-time
coverage reporting; 24 unit tests cover the resolver. Defect 4 is fixed by reading the
checkpoint's own config. Preflight does not catch defect 4, because the refusal is
raised in Trainer initialization rather than at model load.

### Measurement: the RL-era Diamond-30 holdout

Three numbers rest on this holdout: full-spec GRPO 4/30, repair R1 9/30, repair R2
6/30. The 9/30 is published as 30% Gold on a 30-problem holdout (arXiv:2606.06133,
cited at AUDIT.md:12) and restated at docs/formallm.md:25. Three problems apply to all
three numbers.

**The holdout tasks were in the RL prompt pool.** All 30 holdout module names appear
in `data/diamond_gen_topics.json`. `fullspec_dataset.py` defaults `include_topics` to
True, `train_rl_fullspec.py` passes it, and the loader implements no holdout filter;
the repair line inherits the same pool through `collect_ralph_trajectories.py`. The
SFT path does filter by module name (`train.py:110`), and `carve_diamond_holdout.py:17`
states the requirement, so the omission is specific to the RL loaders. Gold specs were
never shown, but the models received TLC-verifier reward on the natural-language
descriptions of the exact 30 evaluation tasks.

**The numbers are not single-shot.** The eval is a four-shot repair loop with verifier
feedback at temperatures 0.5, 0.7 and 0.9. Cross-tabulating result against
`attempts_used`: of R1's 9 fixed, 3 succeeded on shot 0. Single-shot rates are 3/30,
1/30 and 1/30. The published 30% is a pass@4-with-feedback figure and is not labeled
as one.

**The evaluated checkpoint is unverified.** In `repair_pipeline.log`, `merge_lora.py`
fails with an argument error and the pipeline logs `LoRA merge FAILED` at 00:31:19.
The next line begins the eval against Ollama tag `chattla:20b-repair`. No log shows
that tag being rebuilt from the R1 adapter, so we cannot confirm the 9/30 was produced
by the GRPO-trained weights.

Separately, all 228 benchmark CSVs record the model as `chattla:20b`, a mutable tag
rewritten on each redeploy, so no CSV can be attributed to a specific checkpoint.

### Measurement: the Gate-2 harness

Five defects corrupted the numbers the SFT-era training decisions were made on.

`required_signature()` discarded the right-hand side of cfg constant substitutions,
under-specifying framing-A prompts for 13 of 30 holdout specs; 12 of the 15 unsolved
specs were in that set. A serve configured with `--max-model-len 4096` truncated
repair prompts of 4.4k–17k tokens, producing a framing-B regression that did not
reproduce at 32768 (run quarantined). `summary.json` was written from in-memory rows
and understated resumed runs. `api_error` rows are treated as complete by gen-eval's
resume path, so failed draws are silently dropped; this has now occurred twice.
Finally, pass@32 collapses 32 Bernoulli draws per spec into one bit and then sums 30
bits, which is what hid the W4-diamond-gold gain and nearly ended the program on a
false null.

Numbers recorded before 2026-07-29 are not comparable to numbers recorded after,
because the `required_signature` fix changed 13 of 30 framing-A prompts.

Current guards: an aborting trainable-parameter floor, attach-time expert-coverage
reporting, exit-code propagation through PBS, a mandatory preflight against real
weights, ledger-only scoring, and derived-seed decode provenance.

## Questions for the meeting

1. Do we adopt expected-iterations-to-verified as the headline metric, in place of
   single-shot pass rate?
2. Is grammar-constrained decoding worth doing before more fine-tuning, given it needs
   no training compute and cannot confound the training arms?
3. Should the next corpus investment go to task-shape diversity (four environments) or
   to depth in generation and repair alone?
4. The 30-spec holdout is the binding constraint on statistical power: effects below
   roughly 4 points cannot be resolved. Widening it requires an amendment and a
   decontamination pass. Do we spend that?
5. What is published, and with which qualifiers, given the three defects under the
   existing 30% result?

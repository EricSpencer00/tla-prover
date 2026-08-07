# Training methods: what was run and what the failures are attributable to

Covers every training run in the program, from the first 20b SFT (2026-07-12)
through the Amendment-21 reserved run (2026-08-05).

## Method space

Three methods have been used across two eras. The 2026-03/04 era in
`LUC-AI4FM/TLA-Prove` ran DPO and GRPO on gpt-oss-20b; the 2026-07/08 era in this
repo ran LoRA supervised fine-tuning on verifier-accepted outputs
(rejection-sampling fine-tuning, expert iteration) six times against different
corpora. PPO, ORPO, KTO and SimPO appear nowhere.

An earlier draft of this review stated that no RL method had been run. That was
wrong: it searched prove-TLA, which holds the corpus and eval harness, and not
TLA-Prove, which holds the trainers. ROADMAP.md:47's reference to "our existing
repair-GRPO" is accurate.

## RL era, 2026-03-22 to 2026-04-15

Hardware was two 49GB RTX 8000s, which set the batch geometry throughout. All runs
are gpt-oss-20b. Training logs were untracked from the working tree in a later
cleanup and survive only in git history at `e79a250` and `511a492`.

| run | method | reward | outcome |
|---|---|---|---|
| per-action 20b | GRPO | tier staircase, gold 1.0 to bronze 0.1 | no log, checkpoint or eval found; flat reward reported second-hand |
| piecewise DPO | DPO | preference pairs on a VARIABLES→TypeOK→Init→Next curriculum | final loss 0.6661 against ln 2 = 0.6931, accuracy 0.60, margins 0.0599 |
| full-spec | GRPO | 7 weighted components, TLC full 0.35 | 172 steps, mean reward 0.0511, 37 of 172 steps nonzero, entropy 0.44→0.32 |
| repair R1 | GRPO | improvement (after − before), shaped | 965 steps, mean reward 0.1487; 703 of 965 steps had zero reward variance |
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
is zero. Repair R1's mean reward of 0.1487 is the shaping function's hard-coded
"no change" constant of 0.15, so the run sat on the flat part of its own reward for
965 steps. KL stayed between 0.002 and 0.014 throughout, so this was not a
policy-collapse-under-KL failure; it was reward starvation with entropy collapse
alongside (0.44 to 0.32 full-spec, 0.003 to 0.1 on repair). The July attempt records
the endpoint mechanically: at temperature 0.5 the model emitted byte-identical
completions within a group.

We found no evidence of reward hacking and none of verifier false positives. The
reward was not gamed; it was flat.

## SFT era, 2026-07-12 to 2026-08-05

| run | corpus | base | result | comparison |
|---|---|---|---|---|
| v2_sft1 | 39 plain-text pairs | 20b | 0/10, 82% of samples unextractable | directional, k=3 |
| v2_sft2 | 260 harmony pairs | 20b | 2/30 pass@4 (first passes recorded) | directional |
| v2_sft2 | same | 120b | A 11/30 pass@32; B 18/23 pass@32, 6/23 pass@1 | base 12/30; 21/23, 15/23 |
| W2.6 repair-v1 | 508 repair triples | 20b | B 9/23 pass@1, 9/23 pass@4 | base 8/23, 17/23 |
| W4-diamond-gold | 4,119 Opus-teacher rows | 120b | 130/960 = 13.5% per-sample, 16/30 pass@32 | base 66/960 = 6.9%, 12/30 |
| W4DG-genprompt | 4,219 rows, aligned prompt | 120b | 69/896 = 7.7% per-sample, 12/30 pass@32 | base 6.9%, 12/30 |

A seventh arm, Qwen3.6-27B dense, is retracted rather than reported: a
gpt-oss-specific `target_parameters` selector matched nothing on a dense model,
leaving the FFN frozen at 0.0195% trainable while the job exited 0.

Paired two-level bootstrap on byte-identical prompts (n=17 specs): W4-diamond-gold
vs base +0.086, p=0.063; W4DG-genprompt vs base −0.018, p=0.66.

## Configuration defects

Six defects were found, four of which produced a clean exit code on a run that had
not trained what it was supposed to train.

1. `target_parameters` hardcoded for gpt-oss. Dense FFN frozen, 0.0195% trainable,
   exit 0. Invalidated the Qwen arm and, with it, the base-model comparison.
2. `is_moe()` read only the top-level config. Qwen3.5-35B-A3B, with 256 routed
   experts, resolved as dense. Nothing downstream catches this, because the dense
   path yields `all-linear`, which covers attention and the shared expert and clears
   the 0.1% trainable floor on its own.
3. PBS scripts echoed `TRAIN_EXIT=$?` and then exited 0, so PBS recorded success for
   failed runs.
4. `Mxfp4Config(dequantize=True)` was passed for any gpt-oss model rather than for
   MXFP4 checkpoints. On the pre-dequantized bf16 export this marks the model
   quantized without dequantizing, and transformers 5.12.1 refuses to train it
   (job 170856, exit 1 at 3m24s). The environment had drifted from the 5.6.2 the
   recipe was proven against.
5. A two-GPU `CUDA_VISIBLE_DEVICES` hardcode in train.py.
6. The Sophia staging tree carried stale copies of `lora_resolver.py` and `train.py`
   relative to the home tree.

Defects 1–3 and 5 are fixed with an aborting trainable-parameter floor and
attach-time coverage reporting; 24 unit tests cover the resolver. Defect 4 is fixed
by reading the checkpoint's own config. Preflight does not catch defect 4, because
the refusal is raised in Trainer initialization rather than at model load.

## Measurement defects

### The RL-era Diamond-30 holdout

Three numbers rest on this holdout: full-spec GRPO 4/30, repair R1 9/30, repair R2
6/30. The 9/30 is published as 30% Gold on a 30-problem holdout (arXiv:2606.06133,
cited at AUDIT.md:12) and restated at docs/formallm.md:25. Three problems apply to
all three numbers.

**The holdout tasks were in the RL prompt pool.** All 30 holdout module names appear
in `data/diamond_gen_topics.json`. `fullspec_dataset.py` defaults `include_topics`
to True, `train_rl_fullspec.py` passes it, and the loader implements no holdout
filter; the repair line inherits the same pool through
`collect_ralph_trajectories.py`. The SFT path does filter by module name
(`train.py:110`), and `carve_diamond_holdout.py:17` states the requirement, so the
omission is specific to the RL loaders. Gold specs were never shown, but the models
received TLC-verifier reward on the natural-language descriptions of the exact 30
evaluation tasks.

**The numbers are not single-shot.** The eval is a four-shot repair loop with
verifier feedback at temperatures 0.5, 0.7 and 0.9. Cross-tabulating result against
`attempts_used`: of R1's 9 fixed, 3 succeeded on shot 0. Single-shot rates are 3/30,
1/30 and 1/30. The published 30% is a pass@4-with-feedback figure and is not labeled
as one.

**The evaluated checkpoint is unverified.** In `repair_pipeline.log`, `merge_lora.py`
fails with an argument error and the pipeline logs `LoRA merge FAILED` at 00:31:19.
The next line begins the eval against Ollama tag `chattla:20b-repair`. No log shows
that tag being rebuilt from the R1 adapter, so we cannot confirm the 9/30 was
produced by the GRPO-trained weights.

Separately, all 228 benchmark CSVs record the model as `chattla:20b`, a mutable tag
rewritten on each redeploy, so no CSV can be attributed to a specific checkpoint.

### The Gate-2 harness

Five defects corrupted the numbers the SFT-era training decisions were made on.

`required_signature()` discarded the right-hand side of cfg constant substitutions,
under-specifying framing-A prompts for 13 of 30 holdout specs; 12 of the 15 unsolved
specs were in that set. A serve configured with `--max-model-len 4096` truncated
repair prompts of 4.4k–17k tokens, producing a framing-B regression that did not
reproduce at 32768 (run quarantined). `summary.json` was written from in-memory rows
and understated resumed runs. `api_error` rows are treated as complete by
gen-eval's resume path, so failed draws are silently dropped; this has now occurred
twice. Finally, pass@32 collapses 32 Bernoulli draws per spec into one bit and then
sums 30 bits, which is what hid the W4-diamond-gold gain and nearly ended the
program on a false null.

## Attribution

The three candidate causes are all present, in sequence, and they are separable.

**Training method was implicated once, in the RL era, and for a reason that is
diagnosed rather than suspected.** GRPO requires reward variance within a sampled
group, and on this task at this model scale there was none: a group of four
completions to a TLA+ generation prompt nearly always scores identically, because
almost all of them fail to parse. Three separate reward designs were tried against
this (tier staircase, seven-component partial credit, improvement-over-baseline) and
the third was still producing `frac_reward_zero_std = 1` on 73% of steps. The
constraint is a property of the reward landscape, not of any one implementation.

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
dangerous to interpretation**, because four of them exited 0. Defect 1 produced a
written base-model comparison reporting that gpt-oss collapses entropy where Qwen3.6
does not; it was retracted the same day it was committed (`4771fc4d`, `eb111535`).
The retraction was prompted by reading the trainable-parameter percentage, which at
that point nothing enforced. It is now a floor that aborts.

Data quality in the narrower sense (what the corpus teaches) is the open question
rather than an established cause. Between 68% and 74% of sampled failures are
`sany=fail`, meaning the emitted TLA+ does not parse, against 2.1% attributable to
modeling the system incorrectly. Every corpus target is a verified spec, so the
training data contains no instance of the failure mode that accounts for two-thirds
of the errors. Whether supervision on that mode helps is untested; the one attempt
at deterministic parse repair recovered 88 of 454 candidates and flipped no spec to
passing.

The two eras failed against the same wall from opposite sides. GRPO got no gradient
because a group of samples nearly always scored identically, and SFT's failures are
68–74% `sany=fail`; both are the same fact, that most samples do not parse. Under a
policy-gradient objective an unparseable sample carries no learning signal, which is
what starved the reward. Under imitation it is simply absent from the data. This is
the argument for treating parse-level competence as the thing to supervise directly,
and it is also the precondition for RL becoming viable here: reward variance appears
once a meaningful fraction of a sampled group parses.

The most recent result is unexplained. Aligning the SFT prompt to the contract each
survivor was verified under moved framing A from 13.5% to 7.7% per-sample. Gate-2
framing A uses a third prompt shape (gen_eval's), so one candidate is that training
on a fixed template binds the capability to that template, but this has not been
tested. The difficulty probe measures pass rate under the training prompt itself and
would discriminate; it is 436 rows short of complete.

# Training methods: what was run and what the failures are attributable to

Covers every training run in the program, from the first 20b SFT (2026-07-12)
through the Amendment-21 reserved run (2026-08-05).

## Method space

One method has been used: LoRA supervised fine-tuning on verifier-accepted outputs
(rejection-sampling fine-tuning, expert iteration). It has been run six times against
different corpora. No reinforcement-learning or preference-optimization method has
been run: a repository-wide search for GRPO, DPO, PPO, ORPO, KTO and SimPO returns
no trainer, no advantage computation, and no KL term. Apparent matches are substring
collisions ("c*orpo*ra", "end*po*int") and references to other groups' work.
ROADMAP.md:47 refers to "our existing repair-GRPO"; no such implementation exists,
and the phrase should be corrected before publication.

## Runs

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

Separately from training, five defects corrupted the numbers the training decisions
were made on.

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

**Training method is not implicated by any measurement.** It has never been varied,
and no result points at the SFT objective. The two collapse results were explained
by a corpus property and the explanation held when tested.

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

The most recent result is unexplained. Aligning the SFT prompt to the contract each
survivor was verified under moved framing A from 13.5% to 7.7% per-sample. Gate-2
framing A uses a third prompt shape (gen_eval's), so one candidate is that training
on a fixed template binds the capability to that template, but this has not been
tested. The difficulty probe measures pass rate under the training prompt itself and
would discriminate; it is 436 rows short of complete.

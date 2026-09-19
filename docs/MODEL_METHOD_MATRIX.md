# Model × training-method matrix

This is the compact answer to “what did we train?” A model name alone is not a
method. The method includes which parameters could move, the data source, and
the evaluation that was actually completed.

## Terms

| Method | What can change | What it does not mean |
|---|---|---|
| Prompt-only baseline | No model parameters; only the prompt and decoding budget | It is not fine-tuning |
| LoRA / PEFT | Small learned low-rank adapters; base weights stay frozen | It is not full fine-tuning, even when adapters are merged into a copy for serving |
| Full fine-tuning | The selected base-model weights are updated directly | It still does not count without held-out verifier evidence |
| Rejection-sampling / loop | Generates and verifies candidates; may create training data | It is a data/evaluation loop, not a parameter update by itself |
| RL / GRPO | Updates a policy from a reward or preference signal | It is not automatically proof learning; verifier and semantic-audit rules still apply |

## What was measured

| Base model | Method and reachable parameters | Run / data | What happened | Honest conclusion |
|---|---|---|---|---|
| gpt-oss-20b | Prompt-only | Gate-2 frozen baseline, 30-spec holdout | Measured as the untuned comparison arm | Baseline only; no training claim |
| gpt-oss-120b | Prompt-only | Gate-2 frozen baseline, 30-spec holdout | Best frozen baseline: A 12/30 pass@32; B 21/23 pass@32 | Baseline only; no training claim |
| gpt-oss-20b | LoRA / PEFT SFT, expert-reaching recipe | `v2_sft1`, 39 plain-text pairs | 0/10 directional; 82% of samples were unextractable because the harmony final channel was wrong | Pipeline failure; not a capability result |
| gpt-oss-120b | LoRA / PEFT SFT, harmony-formatted targets | `v2_sft2`, 260 pairs | Gate 2 failed: A 11/30 vs 12/30 baseline; B 18/23 vs 21/23 | Fine-tuning did not beat the frozen baseline |
| gpt-oss-20b | LoRA / PEFT SFT, expert-LoRA | W2.6 repair-v1, 508 verified minimal-diff repair pairs | Directional B result was +1 pass@1 and −8 pass@4; diversity collapse reproduced | Fine-tuning shelved for Stage 2 |
| Qwen3.6-27B | Intended LoRA / PEFT SFT | Base-model comparison arm | Retracted: the resolver matched nothing, leaving only 0.0195% trainable | No valid model comparison; bug must be fixed first |
| chattla-v1 artifact | LoRA adapter | W1.3 / Gate-2 candidate | Withdrawn: self-referential base path and attention-only targeting made it unsafe to measure | Not a baseline or training result |

## What has not been done

| Method | State | Meaning |
|---|---|---|
| Full fine-tuning of gpt-oss-20b or gpt-oss-120b | Not run in this program | No claim that all model weights were updated |
| A corrected, architecture-aware Qwen LoRA run | Not run | The retracted run cannot answer the base-model question |
| Stage-3 RL / GRPO prover training | Not run as a protected result | The protected TLAPS target remains 0/119 |
| Any method with a protected promotion | None yet | No checkpoint has passed the current promotion boundary |

The next legitimate training entry must state the base model, update method,
target-module rule, trainable-parameter count, corpus and split, budget, and
the exact SANY/TLC/TLAPS evaluation before it is compared with these rows.

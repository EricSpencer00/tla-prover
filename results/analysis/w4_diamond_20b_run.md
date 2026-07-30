# W4 diamond 20b run — 2026-07-25 (Polaris job 7284822)

Mechanics validation for the W4 graded corpus. **20b, not 120b** — Amendment 17
allows exactly one pre-registered 120b train+eval and this must not spend it.

## Setup

| | |
|---|---|
| corpus | `data/sft_w4_diamond.jsonl` — 508 rows, 51 liveness (10.0%) |
| tier | diamond only (mutation battery produced a mutant, the invariant caught it) |
| model | `openai/gpt-oss-20b`, FSDP2 expert-reaching LoRA (288 params, 24 layers) |
| hardware | 1 node, 2×A100-40GB (of 4), bf16 |
| epochs | 2 (64 steps) |
| runtime | 16m40s, 926k tokens |
| result | **TRAIN_EXIT=0**, checkpoints at `<scratch>/w4train/checkpoints_w4_diamond` (2.1G sharded FSDP; needs the `merge_*` step to become a usable adapter) |

LoRA reached `mlp.experts.lora_A/B` as intended, not just attention.

## Training curve

| step | loss | token acc | entropy |
|---|---|---|---|
| 5 | 1.886 | 0.673 | 1.720 |
| 15 | 1.037 | 0.774 | 1.046 |
| 30 | 0.783 | 0.814 | 0.809 |
| 45 | 0.676 | 0.833 | 0.685 |
| 60 | 0.656 | 0.834 | 0.700 |
| final | 0.909 (avg) | **0.835** | **0.685** |

Loss falls monotonically, accuracy 67% → 84%. Nothing pathological.

## The finding: entropy is the early-warning metric

Entropy fell **60% in 64 steps** and flatlined after step ~35. That is the signature
of the diversity collapse measured twice in W2.6, where pass@1 gained +1 but pass@4
collapsed 17→9 because temperature samples stopped yielding distinct specs (93/115
non-greedy rows produced `no_module_extracted`).

Compared against `moe_fsdp_train_v2sft2.o7247236` — the run that **failed Gate-2 on
exactly that collapse**:

| | v2_sft2 (collapsed) | W4 diamond |
|---|---|---|
| epochs | 4 | 2 |
| entropy start | 1.965 | 1.720 |
| **entropy final** | **0.547** | **0.685** |
| final token accuracy | 0.842 | 0.835 |

**Same terminal accuracy, 25% more entropy retained.** The difference is epochs, not
data: both traces have the same shape, and v2_sft2's extra two epochs drove entropy
into the collapse zone. Our step-30 entropy (0.809) is already near v2_sft2's
step-15 (0.850), so the corpora behave similarly per-step — the endpoint is what the
epoch budget decides.

### What this buys the 120b pre-registration

A concrete, cheap parameter that did not exist before:

- **Cap epochs at 2, or set a hard entropy floor around 0.68**, and log entropy as a
  first-class metric. 4 epochs is what produced the collapsed run.
- Entropy is a **proxy**, not proof. The real test is still pass@k with arms reported
  separately. But it is measurable *during* training, which means the 120b run can be
  stopped before it burns the shot, instead of discovering the collapse at eval.

This is precisely the value of running 20b first, and the reason not to have fired
the 120b last night.

## Caveats

- Eval file == train file, so eval loss is not a generalization signal. Fine for a
  mechanics run; the pre-registered run needs the real holdout.
- 508 rows / 2 epochs is a small budget. The `diamond_gold` run (3,534 rows, job
  7284828, preemptable) is the fuller comparison and was still queued at this writing.
- No pass@k measured here. Nothing in this document claims a capability result.

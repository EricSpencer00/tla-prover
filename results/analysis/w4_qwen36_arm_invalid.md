# The Qwen3.6-27B arm does not test what it claims (2026-07-25)

**Verdict: job 7285843 is not a base-model comparison. Do not read its numbers as
evidence about gpt-oss.** Commit e030bec9 claims "the only variables are the base
model and the chat format." That is false. There are three uncontrolled variables,
and every one of them handicaps Qwen.

## The killer: Qwen's entire FFN was never trained

`src/training/train.py` builds one LoRA config, hardcoded for gpt-oss:

    target_modules    = {q_proj, k_proj, v_proj, o_proj}
    target_parameters = ['mlp.experts.gate_up_proj', 'mlp.experts.down_proj']

`target_parameters` is how the MoE expert stack gets trained. gpt-oss-20b is MoE
(`num_local_experts: 32`), so it matched. **Qwen3.6-27B is dense — `num_local_experts`
is absent.** The selector matched nothing and silently no-op'd. PEFT does not warn.

Confirmed independently in the sharded checkpoint metadata:

| | tensors | LoRA targets present |
|---|---|---|
| 20b `checkpoint-64` | 288 | q, k, v, o, **base_layer, experts** |
| Qwen `checkpoint-32` | 128 | q, k, v, o — **attention only** |

The consequence, straight from the logs:

| | trainable params | % of model |
|---|---|---|
| gpt-oss-20b | 92,454,912 | 0.4401% |
| Qwen3.6-27B | 5,242,880 | **0.0195%** |

**17.6× fewer trainable parameters, with the whole feed-forward stack frozen.**
Qwen was given attention-only adaptation on a task whose knowledge lives in the FFN.

## Confound 2: half the optimizer steps

`configs/accelerate_fsdp2_qwen.yaml` uses 4 processes (27.8B bf16 ≈ 56GB does not fit
a 40GB A100 at 2-way). Same 508 rows and 2 epochs over double the world size = double
the global batch = **32 optimizer steps vs the 20b's 64.** Fewer updates independently
means less drift from the prior.

## Confound 3: the metrics were never comparable

Loss and entropy are per-token quantities over *different tokenizers and different
chat formats* (harmony vs chatml). Absolute cross-model comparison is meaningless.
Only within-run trends are readable, and those are contaminated by confounds 1 and 2.

## What the traces actually show

    gpt-oss-20b (64 steps)   loss 1.886 -> 0.656   entropy 1.72  -> 0.700 (-59%)
    Qwen3.6-27B (32 steps)   loss 1.640 -> 0.993   entropy 0.635 -> 0.818 (+29%)

Qwen's *rising* entropy is not a diversity-preservation win. It is the signature of a
model that barely moved: 0.0195% trainable, frozen FFN, half the steps. Its smaller
token-accuracy gain (+5.5pts vs the 20b's +16pts) says the same thing.

**The 20b entropy finding is unaffected and still stands** — that run's config was
correct for its architecture, and the 2-epoch / entropy-floor-0.68 parameter for the
120b pre-registration survives intact.

## Neither model has been evaluated at all

Both checkpoints are sharded FSDP (`pytorch_model_fsdp_0/*.distcp`) with no merged
adapter. **Neither model has generated a single TLA+ spec.** No claim about capability
— good or bad — is currently supported by anything. The training curves are mechanics
telemetry, not results.

## Harness bugs found

1. **LoRA config is not architecture-aware.** `train.py` must resolve MoE vs dense
   from the config and assert a trainable-parameter floor. A run that silently trains
   0.0195% of the model should abort, not report success.
2. **`w4_qwen.pbs` masks failures.** It echoes `TRAIN_EXIT=$?` but exits 0 regardless,
   so PBS recorded `Exit_status=0` for job 7285833 which had `TRAIN_EXIT=1`. Two
   crashed jobs (7285833, 7285838) looked clean from `qstat`. The PBS script must
   `exit $TRAIN_EXIT`.

## To make the arm valid

Re-run with `target_modules="all-linear"` for the dense case (train.py's own docstring
at line 16 says this covers attention + FFN + MoE), match the optimizer-step count
rather than the epoch count, and compare on downstream TLC-verified pass rate — not
on cross-tokenizer loss. Until then the "is gpt-oss the wrong target?" question is
**untested**, not answered.

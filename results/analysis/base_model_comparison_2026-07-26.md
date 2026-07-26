# RETRACTED — base-model comparison, 2026-07-26

**This document originally claimed a controlled comparison showing gpt-oss
collapses entropy while Qwen3.6-27B does not. That claim is withdrawn.** The
Qwen arm cannot answer the base-model question. See commit 65eaeec3, which
diagnosed this *before* this document was written; I merged that commit into my
history without reading it and restated the invalid claim anyway.

## Why the Qwen arm is invalid

`train.py` hardcodes a gpt-oss LoRA config whose feed-forward coverage rides
entirely on `target_parameters=['mlp.experts.gate_up_proj','mlp.experts.down_proj']`.

- **gpt-oss-20b is MoE** (`num_local_experts=32`) → the selector matched.
- **Qwen3.6-27B is dense** → the selector matched **nothing**, and PEFT no-op'd
  without emitting a warning.

| | trainable params | % | coverage |
|---|---|---|---|
| gpt-oss-20b | 92,454,912 | 0.4401% | q,k,v,o + base_layer + experts |
| Qwen3.6-27B | 5,242,880 | 0.0195% | **attention only — FFN frozen** |

17.6× fewer trainable parameters with the whole feed-forward stack frozen,
confirmed independently in the distcp metadata (288 tensors vs 128).

So Qwen's rising entropy (0.635 → 0.818) is **not** diversity preservation. It
is a model that barely moved, because 0.02% of it was trainable. A frozen model
cannot collapse onto a corpus — that trajectory is what "almost no learning"
looks like, not what a better base model looks like.

## My error, specifically

I checked the LoRA config docstring, saw `target_modules="all-linear"` with a
comment claiming it "covers attention, FFN, AND MoE expert projections," and
concluded the config was architecture-agnostic. I never verified what the
*loaded* config actually contained. The real FFN coverage came from
`target_parameters`, which I did not look at. Reading a comment is not checking
a value.

I compounded it by reporting the checkpoint sizes (Qwen 67M vs gpt-oss 2.1G) as
evidence of a "clean adapter vs MXFP4 bloat." That difference is mostly 5.2M
trainable params vs 92.5M. I had the explanation backwards.

## What survives

**The gpt-oss entropy finding is untouched**, and now has a batch-size control:

| run | job | base | GPUs | steps | entropy start → end | tok acc |
|---|---|---|---|---|---|---|
| A | 7284822 | gpt-oss-20b | 2 | 64 | 1.720 → **0.685** (−60%) | 0.835 |
| C | 7287537 | gpt-oss-20b | 4 | 32 | 1.711 → **0.840** (−51%) | 0.805 |

gpt-oss collapses entropy under both batch configurations. The larger batch
softened it by ~0.15 nats but did not reverse it. The 2-epoch cap / ~0.68
entropy floor parameter for the 120b pre-registration still stands, and is the
useful output of this whole exercise.

**The harness findings survive** and are independent of the comparison. Four
things blocked any non-gpt-oss base model:

1. `use_cache=False` as a `from_pretrained` kwarg — TypeError on
   `Qwen3_5ForCausalLM.__init__`.
2. `Mxfp4Config(dequantize=True)` applied unconditionally — gpt-oss's
   quantization, meaningless for a bf16 checkpoint.
3. `os.environ.setdefault("CUDA_VISIBLE_DEVICES", "0,1")` at `train.py:58` — a
   2-GPU-era default.
4. **The LoRA config is not architecture-aware** — the one that actually
   invalidated the experiment, and the only one that failed *silently*.

**The ChatML format work survives** (`--format chatml`, 6 tests). Harmony is
gpt-oss-specific and would have trained Qwen to emit `<|channel|>final` as
literal text. That was necessary, just not sufficient.

## Nothing here supports a capability claim in either direction

Neither model has been evaluated. Both checkpoints are sharded FSDP with no
merged adapter, and **neither has generated a single TLA+ spec.** Everything
above is training dynamics. pass@k on the frozen holdout with arms reported
separately is the only thing that settles whether gpt-oss is a bad target.

## Fix before re-running

1. **Architecture-aware LoRA resolution** — MoE vs dense — plus a
   trainable-parameter floor that *aborts* rather than reporting success. A
   0.0195% trainable run should never have completed silently.
2. **PBS exit propagation.** My job scripts `echo "TRAIN_EXIT=$?"` but then exit
   0, so PBS recorded `Exit_status=0` for job 7285833 which actually had
   `TRAIN_EXIT=1`. Any automation trusting PBS status would have read those
   crashes as successes.
3. Match optimizer steps across arms (32 vs 64 remains a real, separate
   confound), and stop comparing raw loss/entropy across two tokenizers and two
   chat formats as though the units were shared.

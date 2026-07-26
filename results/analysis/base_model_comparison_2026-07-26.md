# Is gpt-oss a bad target for TLA+? — controlled comparison, 2026-07-26

Three 20b/27b LoRA runs on the **identical** 508-row diamond corpus, 2 epochs.
Only the base model, chat format, and (deliberately, then corrected) the batch
config vary.

## Results

| run | job | base | GPUs | steps | entropy start → end | dir | tok acc | train_loss | runtime |
|---|---|---|---|---|---|---|---|---|---|
| A | 7284822 | gpt-oss-20b | 2 | 64 | 1.720 → **0.685** | **↓ 60%** | 0.835 | 0.909 | 1002s |
| B | 7285843 | Qwen3.6-27B | 4 | 32 | 0.635 → **0.783** | **↑ 23%** | 0.786 | 1.205 | 1472s |
| C | 7287390/537 | gpt-oss-20b | 4 | 32 | 1.711 → **0.840** | **↓ 51%** | 0.805 | 1.154 | 463s |

Run C is the control. B needed 4 GPUs (27.8B bf16 ≈ 56GB), which doubled the
batch and halved the optimizer steps versus A — and fewer, larger updates
independently suppress entropy collapse. C re-runs gpt-oss at B's exact batch
config so the arms are comparable.

## Finding: the direction is real, and it is not batch size

At **matched steps and batch** (B vs C):

- **gpt-oss still collapses**: 1.711 → 0.840, −51%
- **Qwen still rises**: 0.635 → 0.783, +23%

The trajectories point opposite ways under identical training conditions. That
is the result the comparison was built to produce.

Batch size *did* matter, just not enough to explain it: gpt-oss ends at 0.685 on
64 steps and 0.840 on 32 steps, so the larger batch softened the collapse by
about 0.15 nats. It did not reverse it.

The two models behave qualitatively differently, not quantitatively:

- **gpt-oss starts uncertain (1.71) and becomes progressively deterministic.**
  That is the classic overfit/collapse signature, and it is the same shape that
  preceded the W2.6 Gate-2 failure (pass@1 +1, pass@4 17→9, 93/115 non-greedy
  rows `no_module_extracted`).
- **Qwen starts confident (0.64) and becomes more diverse.** It is not narrowing
  onto the corpus; entropy rises monotonically across all six logged points.

## What this does NOT show

- **Absolute entropy is not comparable across tokenizers.** gpt-oss ~200k vocab,
  Qwen ~248k. Note gpt-oss actually *ends* higher in absolute terms (0.840 vs
  0.783). Only the direction is robust.
- **No capability claim.** Neither model has generated a single TLA+ spec here.
  pass@k on the frozen holdout, arms reported separately, is the only thing that
  settles "bad target". Everything above is training dynamics.
- Eval file == train file in all three runs, so eval loss carries no
  generalization signal.
- n=1 per arm. No seed variation.

## Secondary observations

**Cost.** gpt-oss trained 3.2× faster (463s vs 1472s) — MoE with ~3.6B active
against a 27.8B dense model. Whatever else is true, gpt-oss is much cheaper per
step.

**Checkpoint size.** Qwen 67M, gpt-oss 2.1G, same LoRA rank and corpus. The
gpt-oss figure is the MXFP4-dequantization path writing far more than adapter
weights, and it is paid again at every checkpoint, merge, and serve.

**The harness was gpt-oss-shaped.** Three unconditional assumptions had to be
removed before any other base model could load at all:

1. `use_cache=False` passed to `from_pretrained` — a TypeError on
   `Qwen3_5ForCausalLM.__init__`; it belongs on the config.
2. `Mxfp4Config(dequantize=True)` applied unconditionally — gpt-oss's
   quantization, meaningless for a bf16 checkpoint.
3. `os.environ.setdefault("CUDA_VISIBLE_DEVICES", "0,1")` at `train.py:58`, a
   2-GPU-era default that caps any run at 2 devices.

All three are now gated (`is_gpt_oss`) or overridable; backup at
`~/ChatTLA/src/training/train.py.bak_pre_qwen`. **This is a finding in its own
right: the "is gpt-oss the problem" question was not testable before now**, so
the corpus has been carrying blame it may not deserve.

**Format.** Harmony is gpt-oss-specific. Rendering it for Qwen would have taught
the model to emit `<|channel|>final` as literal text. `harness/corpus_prep.py`
now supports `--format chatml`; Qwen's `eos_token` is `<|im_end|>`, which is what
the chatml rendering terminates on.

## Next

The cheap, decisive step is pass@k on the holdout for run B's adapter vs the
Qwen base — that converts a dynamics observation into a capability result. It
needs a merge + serve, which is the same path documented for the gpt-oss
adapters.

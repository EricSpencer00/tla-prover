# The dense-vs-MoE trainability check (2026-08-03)

**Status: the PLAN.md (b) precondition on the reserved pre-registered run is met.
Both architectures now attach with FFN coverage, measured on real weights. The
base-model question is still open — this check does not answer it, and reading a
verdict out of it would repeat the error that retracted the Qwen arm.**

PLAN.md (b) held the reserved run until "(1) lands and a valid dense-vs-MoE
trainability check exists." (1) is `ef1981d`; this is the check.

## What was measured

Sophia job **170815** (4×A100-40GB, `single-node`), ChatTLA at **`4344909`**.
Both arms: 4 processes, per-device batch 1, accum 8, `max_steps=8` — identical.
Only the base model, its chat format, and its FSDP wrap class differ. That
retires the 32-vs-64 optimizer-step confound of the original comparison.

| Arm | Trainable | Params | LoRA tensors | Expert tensors |
|---|---|---|---|---|
| Qwen3.6-27B (dense) | **0.2165%** | 58,363,904 / 26,954,362,368 | 992 | 0 (correct — dense) |
| gpt-oss-20b (MoE) | **0.4401%** | 92,454,912 / 21,007,212,096 | 288 | **96** |

The dense arm is **11.1× more trainable parameters** than the retracted run's
0.0195%, and `all-linear` also reached Qwen's linear-attention projections
(`layers.24.linear_attn.in_proj_b`) that an attention-only list never would.
The MoE arm reproduces the historical healthy figure to four decimal places.

Reproducible: job **170812** produced identical percentages at `46e3b7f`, where
the report was still emitted after the device-alignment loop. Same numbers from
two different code placements.

Training proceeded (8 steps, both arms exit 0):

    dense  loss 1.641 -> 1.033   token acc 0.7211 -> 0.7812   52.0 s/step
    MoE    loss 1.952 -> 1.467   token acc 0.6654 -> 0.7247   14.5 s/step

## What this does NOT license

1. **Not a base-model verdict.** Eight steps under LR warmup. The entropy traces
   are not comparable across arms: the MoE arm starts at 1.75 and the dense arm
   at 0.654, which is a tokenizer-and-chat-format difference (harmony vs chatml),
   not a property of either model. That is blocker 3, still live.
2. **The arms do not have equal capacity.** 0.2165% vs 0.4401% is a ~2× gap in
   trainable fraction. The silent freeze is gone; a *controlled* dense-vs-MoE
   comparison additionally needs rank chosen to equalize trainable fraction.
3. **Venue assumption is wrong.** PLAN.md:258 prefers "Sophia single-node
   (8×80GB)". `sophia-gpu-12` served all four jobs today as **4×A100-40GB**.
   Qwen3.6-27B at 56GB bf16 therefore needs the 4-way shard here exactly as it
   did on Polaris. Recheck before planning the reserved run around 80GB.

## A second silent bug, found while doing this

`is_moe()` read only the top-level config. Qwen3.5/3.6 use wrapper configs that
carry the expert count **only on the nested text config**, so
**Qwen3.5-35B-A3B — 256 routed experts — resolved as dense.**

That is strictly worse than the bug this work started on, because nothing
downstream catches it: dense resolution yields `all-linear`, which covers
attention and `mlp.shared_expert` (both `nn.Linear`) and clears the 0.1%
trainable floor on its own. The 256 routed experts would have trained frozen and
the run would have exited 0.

Verified against the real cached configs on Sophia: Qwen3.5-MoE stores routed
experts as packed 3D params named `mlp.experts.gate_up_proj` / `down_proj`,
shape `(256, 1024, 2048)` — byte-identical naming to gpt-oss. So
`target_parameters` was never gpt-oss-specific. Fixed in `c5a94b8`.

Qwen3.6-27B is nested *and* genuinely dense, so it still correctly resolves to
`all-linear`. That is why today's dense arm is unaffected.

## Blocker status against PLAN.md (b)

1. **Architecture-aware resolution + aborting floor — DONE and verified.**
   `ef1981d` (dense path actually governed by the resolver; it was dead code
   before), `c5a94b8` (nested configs), `4344909` (coverage reported at attach
   time, before anything can die first). 24 unit tests.
2. **PBS exit propagation — verified, not newly fixed.** Every `.pbs` in the
   ChatTLA repo already propagates `TRAIN_EXIT`, as does `w4_trainability_check.pbs`.
   `preflight_120b.py` check 5 scans for the regression.
3. **Matched optimizer steps — done for this check** (8/8, same batch and accum).
   The cross-tokenizer loss/entropy comparison remains invalid and unfixed.

## Cost and failures

Three failed attempts preceded the good run; all three were environment, not
coverage, and cost ~2 minutes of node time total.

- **170803** — MLflow in Sophia's `frs` conda env *raises* on a `file://`
  tracking store; Polaris's `.venv` has an older MLflow that warns. Died at
  `set_experiment()` before touching a GPU. Fixed in `46e3b7f` via
  `MLFLOW_ALLOW_FILE_STORE`, so prior runs' metrics stay readable in the same store.
- **170811** — `libgomp: Thread creation failed`. My job script was derived from
  the Polaris W4 scripts, which omit the `OMP_NUM_THREADS=8` / `MKL_NUM_THREADS=8`
  exports that every working `scripts/qsub_*sophia*.pbs` sets. Four ranks × a
  128-core OpenMP default exhausted thread creation.
- **170812** — succeeded, but see the note above: it attached correctly and would
  have lost its trainable-% had it crashed 60 lines later, which is what 170811
  did. That is the reason for `4344909`.

Also fixed in passing: `train.py`'s default MLflow experiment is
`ChatTLA-gpt-oss-20b` for **any** non-prover model, so the retracted Qwen arm
logged its metrics under a gpt-oss-named experiment. Both arms here pass an
explicit `--experiment-name`.

## Artifacts

- Job logs: `~/ChatTLA/w4_trainability_check.o{170803,170811,170812,170815}` (Sophia)
- Per-arm logs: `/grand/EVITA/eric-spencer/w4train/trainability_check_170815/`
- MLflow: `ChatTLA-w4-trainability-qwen36-dense`, `ChatTLA-w4-trainability-gptoss20b-moe`
- Job script: `~/w4_trainability_check.pbs` (Sophia; not yet in the repo)
- Code: `LUC-AI4FM/ChatTLA` branch `fix/training-blockers-lora-floor`, unmerged

# W4 train readiness — 2026-07-25

## TL;DR

The **trainable set is done, verified, committed, and staged on ALCF.**
The **train did not launch.** It is blocked on one thing: a **Polaris** OTP.

---

## What is ready

Rendered by `python3 -m harness.corpus_prep sft --min-tier N`, all harmony-verified
(final channel + ```` ```tla ```` + ```` ```cfg ```` in every target), zero duplicate
seed_keys, exclusions and keep-last honored:

| file | rows | liveness | ~tokens | top family |
|---|---|---|---|---|
| `results/analysis/sft_w4_diamond.jsonl` | 444 | 19 | 342k | mutex_locks 28.4% |
| `results/analysis/sft_w4_diamond_gold.jsonl` | 3,260 | 85 | 2.6M | mutex_locks 36.0% |
| `results/analysis/sft_w4_all_graded.jsonl` | 3,942 | 85 | 3.1M | mutex_locks 35.7% |

That is a 3-point ablation curve mirroring TLA-Prover Table 4 (diamond-only 1,053
beat silver-and-above 4,210: 13.3% vs 6.7%). Grading rationale and tier definitions
are in `harness/w4_corpus.py`.

**Staged on ALCF** (`/home` and `/grand` are shared between Sophia and Polaris, so
these are visible from both):

- `~/ChatTLA/data/sft_w4_diamond.jsonl` (444)
- `~/ChatTLA/data/sft_w4_diamond_gold.jsonl` (3,260)
- `~/moe_fsdp_train_w4_diamond_gold.pbs` — 20b, 3 epochs, FSDP2 expert-reaching LoRA
- `~/moe_fsdp_train_w4_diamond.pbs` — 20b, 6 epochs (smaller corpus, more passes)

Both PBS scripts write checkpoints to `/grand/EVITA/eric-spencer/w4train/`, **not**
`$HOME` — see the quota note below.

## The blocker

The proven recipe (`~/moe_fsdp_train_v2sft2.pbs`) carries
`#PBS -l select=1:system=polaris`, and `~/ChatTLA/.venv` is a **Polaris** venv — its
interpreter symlinks to `/soft/applications/conda/2025-09-25/mconda3/bin/python3`,
which does not exist on Sophia.

The open ControlMaster socket is to **Sophia**. Sophia's scheduler is
`sophia-pbs-01`; it has no `debug`/`prod` queues and no Polaris vnodes, so `qsub` of
the Polaris script fails:

```
qsub: vnode_resource_hook.py failure: 'NoneType' object has no attribute 'resources_default'
```

**To unblock:** open a Polaris socket and submit. Everything else is in place.

```bash
ssh -fN polaris
```

then

```bash
ssh polaris 'qsub ~/moe_fsdp_train_w4_diamond_gold.pbs'
```

## Sophia-native fallback — attempted, not finished

Sophia is otherwise viable: PyPI reachable from the login node, 8 GPUs/node,
`by-node` walltime up to 24h. A Sophia venv was attempted at
`/grand/EVITA/eric-spencer/venvs/sophia-train`. It got as far as importing
transformers/accelerate/trl/mlflow, then hit an unfixable leak:

`--system-site-packages` exposes Sophia conda's `transformer_engine`, which `peft`
unconditionally probes for, and which is broken on that node:

```
libtransformer_engine.so: undefined symbol: cublasLtGroupedMatrixLayoutInit_internal,
version libcublasLt.so.13
```

A hermetic rebuild (no system site-packages, own torch) was launched at
`/grand/EVITA/eric-spencer/venvs/sophia-train-clean`; script `~/rebuild_hermetic.sh`,
log `~/rebuild_hermetic.log`. **Check the log before trusting it.** Even if the
imports pass, FSDP2 + gpt-oss triton kernels on torch 2.11/py3.13 is untested on
Sophia — the Polaris path is proven and should be preferred.

Also note: `harness/corpus_prep.py` and the PBS scripts default to
`MODEL_ID = openai/gpt-oss-20b`. Both `gpt-oss-20b` and `gpt-oss-120b` are cached at
`/grand/EVITA/eric-spencer/hf-cache/hub/`. Pass `--base-model` to switch.

## Two things that need your call

1. **The 120b run is pre-registered and single-shot.** Per Amendment 17 the flywheel
   is loop-only and fine-tuning is shelved; the design doc allows exactly ONE
   pre-registered 120b train+eval, with arms reported separately. The staged scripts
   are 20b deliberately — a 20b run is mechanics validation and costs nothing
   against that budget. Firing 120b overnight without a written pre-registration
   would spend the one shot. I did not do it.
2. **Which tier is the real training corpus.** `diamond_gold` (3,260) is the
   recommendation; `diamond` (444) is the aggressive filter the literature favors
   and is also the best family-balanced set. The ablation is the interesting
   experiment and all three files exist.

## Housekeeping found along the way

- **ALCF home is over quota: 101G against a 45G limit.** Writes still succeed (soft
  limit) but a 3MB scp already failed once mid-transfer. Nothing was deleted —
  18G sits in `~/ChatTLA/outputs/` across ~12 old checkpoint dirs and ~4.5G in
  `~/adapter_*_reconstructed/`. Reclaiming that is your call; all new output is
  routed to `/grand`.
- **The Discord notifier is dead**: `hermes send` returns
  `Discord API error (401): Unauthorized`. The OTP ping in
  `tools/otp_nag.sh` cannot reach you until that token is refreshed.

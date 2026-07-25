# W4 train readiness — 2026-07-25

## Status

**Training is running on Polaris.** The corpus is graded, the export bug is fixed,
and the proven recipe is executing.

| job | queue | corpus | state |
|---|---|---|---|
| `7284822` | debug (1h) | diamond — 508 rows, 51 liveness | **RUNNING**, 4× A100-40GB |
| `7284828` | preemptable (6h) | diamond_gold — 3,534 rows, 220 liveness | queued, smoke-gated |

Both are **20b**. The 120b remains unfired — see "Not done deliberately" below.

## The corpus

Rendered by `python3 -m harness.corpus_prep sft --min-tier N`, harmony-verified
(final channel + ```` ```tla ```` + ```` ```cfg ```` in every target), zero duplicate
seed_keys, exclusions and keep-last honored. Cut against corpus 4,314 / 220 liveness:

| file | rows | liveness | top family |
|---|---|---|---|
| `sft_w4_diamond.jsonl` | 508 | 51 (**10.0%**) | mutex_locks 29.3% |
| `sft_w4_diamond_gold.jsonl` | 3,534 | 220 (6.2%) | mutex_locks 35.8% |
| `sft_w4_all_graded.jsonl` | 4,216 | 220 (5.2%) | mutex_locks 35.5% |

Tier definitions and rationale: `harness/w4_corpus.py`. Diamond is the
mutation-catch-only tier — the one TLA-Prover Table 4 found beat a corpus 4× its
size (13.3% vs 6.7%). It also carries the best family balance in the corpus, because
the mutation filter de-skews as a side effect.

## Cluster notes

**Polaris is the working path.** `~/ChatTLA/.venv` (py3.12.11) resolves here and the
pinned stack imports clean: torch 2.11.0+cu128, transformers 5.6.2, peft 0.19.1,
accelerate 1.13.0, trl 1.2.0.

Queue facts worth not rediscovering:
- `debug` — max 1h, max 2 nodes. Sized diamond at 2 epochs (1,016 samples) against
  the proven v2sft2 debug load (260 rows × 4 = 1,040).
- `prod` — **`resources_min.nodect = 10`**. A `select=1` job is rejected with
  "Job violates queue and/or server resource limits".
- `preemptable` — min 1 node, max 72h. This is the queue for long single-node runs.

**Sophia does not work for this and is not worth retrying.** Its `.venv` is a Polaris
venv (interpreter symlinks into `/soft/applications/conda/2025-09-25`), `sophia-pbs-01`
has no polaris vnodes, and the cluster was fully saturated — all 23 nodes
job-exclusive, `single-gpu` showing 0 running against 10 queued, jobs ahead holding
24h walltimes. A job sat queued 6h12m and never started.

A working Sophia-native venv does now exist at
`/grand/EVITA/eric-spencer/venvs/sophia-train-clean` (build script
`~/rebuild_hermetic.sh`) if capacity ever frees up. Build it **without**
`--system-site-packages` — conda's `transformer_engine` is broken there
(`undefined symbol cublasLtGroupedMatrixLayoutInit_internal`) and peft probes it
unconditionally.

## Not done deliberately

**The 120b run.** Amendment 17 shelves fine-tuning and the design doc allows exactly
ONE pre-registered 120b train+eval with arms reported separately. Firing it now would
spend that shot on a corpus that is **5.1% liveness against a public TLA+ rate of
23–34%** — the first thing a reviewer with `grep` will find.

The loop is closing that gap fast: 85 → 220 liveness in about twelve hours, with
waves landing clean 25L/25S splits. The 500-liveness floor is roughly a day out.
The right sequence is: let the 20b runs validate mechanics, let the loop hit the
floor, re-render, write the pre-registration, then spend the 120b shot once.

## Housekeeping

- **ALCF home quota RESOLVED 2026-07-25: 101G → 29.11G against 45G.** All training
  output stays routed to `/grand/EVITA/eric-spencer/w4train/`. What was reclaimed,
  and the evidence each was safe:
  - **39G deleted** — `~/.cache/huggingface/hub/models--EricSpencer00--chattla-20b`.
    Triple-checked: every blob hash also present at identical size in
    `/grand/EVITA/eric-spencer/hf-cache/hub/` (which holds 3 snapshots vs home's 1),
    AND the Hub repo `EricSpencer00/chattla-20b` carries the same
    `model.safetensors` (41,829,561,832 B) and `adapter_model.safetensors`
    (7,988,016 B). Two independent copies survive.
  - **13G deleted** — `~/.cache/pip`. Pure wheel cache; all venvs already built.
  - **18G relocated** — `~/ChatTLA/outputs/` →
    `chattla_artifacts/home_outputs_archive`, verified byte-exact
    (18,745,504,074 B both sides, 6,866 files, empty `rsync -an` diff) before the
    source was removed. `~/ChatTLA/outputs` is now a symlink to that path, so any
    script referencing it still resolves. The *merged* models for these checkpoints
    (`merged_v2_sft1/sft2/ablate_e4/repair_v1`) already lived in EVITA.
  - **4.5G relocated** — `~/adapter_*_reconstructed/` →
    `chattla_artifacts/home_adapters_reconstructed`, byte-verified
    (4,700,928,628 B) before removal.
  - **Deliberately untouched**: `~/ChatTLA/.venv` (9.8G, the working Polaris venv —
    the queued job's interpreter), `~/.conda/envs/frs` (10G, FormalRewardSignal),
    `~/ChatTLA/.git`. Post-cleanup dry-import under the exact job env is green:
    torch 2.11.0+cu128 / transformers 5.6.2 / peft 0.19.1 / accelerate 1.13.0 /
    trl 1.2.0, `src.training.train` imports, job inputs present.
- **The Discord notifier is dead**: `hermes send` returns
  `Discord API error (401): Unauthorized`, so `tools/otp_nag.sh` cannot reach Eric.
- The cloud routine cannot delegate — its `allowed_tools` has no `Task`, so each wave
  runs 50 cells in one long-context session. Adding `Task` would let it dispatch a
  subagent per shard and cut the cache-read cost, which dominates spend at roughly
  41:1 over fresh tokens. Not changed mid-run: the loop is healthy and about a day
  from its floor, and breaking it now costs more than the tokens save.

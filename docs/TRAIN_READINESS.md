# W4 train readiness — 2026-07-25

> Historical snapshot. Superseded by the W4-diamond-gold 120b runs of 2026-07-29/30
> ([W4DG_GATE2_SESSION_2026-07-29.md](W4DG_GATE2_SESSION_2026-07-29.md)); kept for the
> corpus cut and the deferral reasoning it records.

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

**A second cluster in the same facility does not share the venv.** Its `.venv` was
built for the first cluster (interpreter symlinks into the shared conda tree), its PBS
server exposes no vnodes of the other type, and it was fully saturated at the time —
all 23 nodes job-exclusive, a job sat queued 6h12m and never started. A
cluster-native hermetic venv on Lustre scratch works if capacity frees up. Build it
**without** `--system-site-packages`: the site conda's `transformer_engine` is broken
there (`undefined symbol cublasLtGroupedMatrixLayoutInit_internal`) and peft probes it
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

- Training output is routed to Lustre scratch, not to a home directory — home quotas
  at this facility are far too small for HF caches plus checkpoints, and the failure
  mode is a job that dies mid-run rather than a clear error.
- Post-cleanup dry-import under the exact job environment is green: torch
  2.11.0+cu128 / transformers 5.6.2 / peft 0.19.1 / accelerate 1.13.0 / trl 1.2.0,
  `src.training.train` imports, job inputs present. Run this before every submission
  — see the preflight discipline in [W4_CELL_RULES.md](W4_CELL_RULES.md).

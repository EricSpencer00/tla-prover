# TLA+ Prover — State Audit (2026-07-02)

Goal: 100% verified pass (SANY → TLC → TLAPS/Apalache) on the FormaLLM corpus (~206 specs),
then scale to the 2,600+ raw GitHub-scraped set.

## Where we actually are

| Result | Corpus | SANY | TLC (real pass) | Source |
|---|---|---|---|---|
| chattla-20b v22, self-correct + best-of-5 | internal 20-item suite | 14/20 (70%) | 9/20 (45%) | HF model card; `ChatTLA/outputs/manifests/hf_publish_readiness.chattla_20b_fc128best.json` |
| chattla-20b, **single-shot** | internal 20-item suite | 4/20 (20%) | 1/20 (5%) | HF model card |
| TLA-Prover paper (SFT + repair-GRPO) | 30-problem holdout | 80% Silver | 30% Gold/Diamond | arXiv:2606.06133 |
| Opus 4.7 (1M) 0-shot — best baseline | FormaLLM val (30) | 19/30 (63%) | **7/30 (23.3%)** non-vacuous | `FormaLLM/benchmarks/data_matrix.csv`, `ABLATION_REPORT.md` |
| Opus 4.7 agent-RAG (self-retrieved exemplars) | FormaLLM val (30) | 19/30 | 4/30 (16.7%) | same |
| Prover adapter checkpoint-200 (proof mode) | 18 eval specs | parse 3/18 | **proved 0/18** | `codex/tla-prover-artifacts-and-gates` branch, LUC-AI4FM/TLA-Prove |
| Untuned 30-model sweep (best) | 205 specs / 26 semantic | 26.6% | 8.6% | arXiv:2606.05792 |

**Headline: best honest TLC pass anywhere is ~23–45% depending on subset and inference budget.
TLAPS proving is at 0%. No eval of chattla-20b on the full 206-spec corpus exists at all.**

## Key findings

### 1. The SOPHIA/LoRA suspicion is confirmed — the fine-tune is misconfigured, not "full training"
- The run was a **LoRA (r=8, α=16) fine-tune of openai/gpt-oss-20b**, launched via 13+ PBS scripts
  (`ChatTLA/ChatTLA/scripts/qsub_sophia_*.pbs`, 4 GPU / 480GB / 4h walltime). It did run; it was never full training.
- Published HF adapter targets **q/k/v/o attention only** — the MoE expert MLPs (where most of
  gpt-oss-20b's capacity lives) got no gradient signal. Local `lora_config.yaml` says `all-linear`,
  so what was published disagrees with what the config intends.
- `adapter_config.json` is broken: `base_model_name_or_path` points **at chattla-20b itself**
  (self-referential — PEFT stacks the adapter onto already-merged weights), and
  `layers_to_transform: [0..63]` vs the model's actual 24 layers.
- One local config shows a **57-example SFT corpus for 10 epochs**; HF dataset
  `chattla-tla-prover-corpora-v1` has 1,125 rows; the paper says 1,053. Multiple runs are conflated.
- The HF repo is 373 GB: merged bf16 weights **duplicated** (safetensors + pytorch_model.bin,
  41.8 GB each — MXFP4 was dequantized, 3× native size), 13 Q8_0 GGUFs (v10–v22), plus
  optimizer.pt/rng_state.pth trainer litter at root.

### 2. Contamination undermines the target as stated
The model card states the 1,330-row training corpus **includes all 205 canonical FormaLLM
benchmark examples**. Decide explicitly which game we're playing:
- **Closed-book (memorize the 206):** legitimate only as an artifact ("verified corpus regeneration"),
  and even then the model can't reproduce specs it trained on — so training isn't the bottleneck.
- **Generalization:** then the 206 must come OUT of training data and the paper's 30-holdout
  (or the planned 100–200 holdout) is the real benchmark. 100% on a 30-spec holdout ≠ 100% prover.

### 3. TLAPS and Apalache don't exist in the stack
- `tlapm` and `apalache-mc`: **not installed** locally; **zero integration** in tla_benchmark
  pipelines. Only tla2tools.jar (SANY/TLC) is wired in.
- The "108/108 TLAPS" HF artifact covers 18 known modules (299/299 obligations) and its own card
  says it is not a generalization claim. The prover branch measured **0/18 proved**.
- Also structural: only **134/206 specs have .cfg files** — TLC can't even run on 72 specs
  without generating configs. That alone caps TLC coverage at ~65%.

### 4. RAG is not the shortcut
The agent-RAG ablation (self-retrieved exemplars, Opus 4.7 1M) **underperformed 0-shot**
(16.7% vs 23.3%) — context dilution and bad self-retrieval. Fixed few-shot also underperformed
0-shot (heavy PlusCal exemplars steer wrong). What actually moves the number, per both papers and
the v22 card, is **verifier-in-the-loop repair**: single-shot 1/20 → best-of-5 + self-correct 9/20.

### 5. Repo state, briefly
- **LUC-AI4FM/TLA-Prove**: the real pipeline repo (data → SFT/GRPO → eval). Main HEAD is a
  *revert* of PR #4 (corpus expansion backed out). Codex branches = prover diagnosis (0/18) +
  cluster launcher plumbing. Zero issues filed.
- **TLA-Extraction**: the "2000+" set = 2,628 raw scraped files / 3,979 parsed artifacts; 206 canonical.
- **tla_benchmark**: 206 specs (205 .tla, 134 .cfg), Redis+RQ + Streamlit harness — the right
  skeleton for a corpus-wide sweep.
- **training-tla-model**: paper template is an unpopulated stub. **FormaLLM-Reverse**: framework
  only, no committed metrics. **tla-verf**: empty.

## Gap to 100% — and the one-shot SOPHIA job

Fine-tuning harder is not the path: the paper's own SFT+GRPO ceiling is 30% Gold, and prompting
plateaus near zero. The distance from ~30% to 100% on a fixed 206-spec corpus closes with
**verifier-guided search per spec**, not model quality: generate → SANY/TLC feedback → repair,
best-of-N, escalating budget per spec until it passes. On a *fixed finite corpus*, that is an
embarrassingly parallel compute problem — exactly one Argonne job.

**Before submitting (local, ~a day):**
1. Fix `adapter_config.json` on HF (correct base model, layers) or just serve merged GGUF; stop
   shipping the broken adapter.
2. Wire `tlapm` + `apalache-mc` into the tla_benchmark harness (container/spack env for Sophia);
   pass = SANY ∧ TLC-non-vacuous (∧ TLAPS obligations where proofs exist).
3. Generate/repair the 72 missing .cfg files (LLM-drafted, human-sanity-checked) so all 206 are checkable.
4. Pick the honest target: 206 closed-book regeneration AND the 30-spec decontaminated holdout,
   reported separately.

**The job (one PBS submission, resumable):**
- Sweep all 206 specs × {chattla-20b, frontier API model} × repair loop (max K rounds, best-of-N),
  TLC as reward/filter, per-spec escalation; emit a 206-row matrix
  (spec, method, SANY, TLC, TLAPS, Apalache, rounds-to-pass, tokens spent).
- Expected outcome based on current numbers: repair loop should lift 23–45% into the 60–85% band;
  the residue (quantifier-heavy, case-analysis, big-state specs) is the actual research problem —
  that residue list, not another training run, is what the next paper/iteration needs.

## Pointers
- Ablation analysis: `FormaLLM/benchmarks/ABLATION_REPORT.md`
- Publish-readiness eval: `ChatTLA/ChatTLA/outputs/manifests/hf_publish_readiness.chattla_20b_fc128best.json`
- Sophia scripts: `ChatTLA/ChatTLA/scripts/qsub_sophia_*.pbs`
- Prover diagnosis: branches `codex/tla-prover-artifacts-and-gates`, `codex/tla-prover-proof-repair-primary-run`
- HF: model `EricSpencer00/chattla-20b` (+ -gguf, -v15, -prover-v3); datasets
  `chattla-tla-prover-corpora-v1` (1,125 rows), `chattla-tla-prover-108-108`
- Papers: arXiv:2606.06133 (TLA-Prover), arXiv:2606.05792 (Can LLMs Write Correct TLA+?)

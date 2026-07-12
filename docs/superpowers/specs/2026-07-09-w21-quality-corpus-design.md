# W2.1 Quality Corpus — Rejection-Sampling Fine-Tuning Pipeline

**Date:** 2026-07-09
**Status:** design, pending Eric review
**Owner:** prove-TLA / chattla-v2 (Gate 2)

## Goal (locked 2026-07-09)

Produce a system that emits **guaranteed-correct TLA+ specs from an LLM**. The correctness
guarantee is **structural — it comes from the verify-until-correct loop (SANY + TLC +
non-vacuity + repair), not the model weights.** The model's job is to make that loop
*converge* (high first-pass / few-iteration yield) and to produce *meaningful* specs, not
merely valid ones. Success is measured by **Gate 2**: a fine-tuned `chattla-v2` must beat the
frozen E2.c baseline (gpt-oss-120b: framing A 2/30 & 12/30, framing B 12/23 & 20/23; ≥ all
four cells, > one).

**Non-goals / deferred:** the TLAPS Stage-3 prover (unbounded proofs) is a separate, deeper
capability and is **out of scope** here — TLC model-checking + non-vacuity already yields
verified-correct bounded specs, which is the north star. From-scratch model training is
rejected (a ~1k-spec corpus cannot train base competence).

## Method: rejection-sampling fine-tuning (RFT / STaR)

Fine-tune **gpt-oss-120b** (general reasoning from pretraining + TLA+ specialization). The
loop is a verifier; RFT turns "keep what survives the verifier" into training signal:

```
seed (NL) → [Ralph loop: property-freeze → gen → SANY → inv-gate → TLC
             → thin/trivial/liveness/mutation gates, ≤8 iters] → survivor?
     survivors (valid ∧ non-vacuous ∧ decontaminated) → SFT/PEFT gpt-oss-120b → Gate 2
```

Reference loop: `github.com/LUC-AI4FM/tla-generator` (`backend/app/ralph.py`,
`adequacy.py`, `prompts.py`).

## Architecture — two workstreams over `data/chattla-corpora-v2`

### Workstream 1 — `adequacy` battery (deterministic, zero model calls)

New resumable funnel stage (follows the existing `dedup/decontam/sany/tlc/assemble` pattern in
`harness/w21_funnel.py`). Per tier1/tier3 spec (needs a `.cfg` + TLC pass):

- **mutation-sensitivity (star metric)** — reuse `harness/mutation.py::run_mutation_for_spec`
  (deterministic regex battery, reproducible — this is why we do NOT use tla-generator's
  model-generated mutant). `mutation_catch_rate = caught / applicable`.
  - **Review fix (#4): attribute catches to which invariant fired.** The deterministic
    mutation battery currently marks a mutant 'killed' on any TLC failure
    (`tlc_st != 'pass'`), which counts a mutant that only breaks TypeOK the same as one
    breaking the real safety property — gameable exactly the way this project exists to
    catch. Fix: count a catch only when a NON-TypeOK safety property is violated; report
    `mutation_catch_rate` over that attribution. Keep the deterministic battery for
    reproducibility.
- **trivial-invariant** — port `check_trivial_invariants` (`Inv == TRUE`) from tla-generator.
- **thin-model** — distinct-states `< 3` (`min_interesting_states`); re-derive states in the
  battery TLC run since tier3's `tlc_states_found` is 0.
- **structural features** — #VARIABLES, #Next-disjuncts, #defs, temporal-op use
  (`[]`/`<>`/`WF`/`SF`), non-comment LOC, comment ratio, EXTENDS depth.

**Output:** soft-labels on **all 949** (nothing deleted) + a named advisory manifest
`manifest_tier_quality.jsonl` where `quality_gold = non-vacuous ∧ not-thin ∧ no-trivial-inv ∧
mutation_catch_rate ≥ 0.5`. This is both a corpus tier *and* the reward filter reused for W2.

### Workstream 2 — `generate` loop (the RFT sampler; only Sophia spend)

New harness module porting the tla-generator Ralph loop into prove-TLA. Per NL seed, ≤8 iters:
property-freeze → generate → SANY → invariant-gate → TLC → thin/trivial/liveness →
**deterministic mutation gate (Workstream-1 battery, not a model mutant)** → converge or
reject. Model = gpt-oss-120b on Sophia via `harness/repair.py::make_model`. Log the **yield
rate** (survivors / attempts — the "how much shit we avoid throwing" number).

**Seeds are anchored to GOLD specs, not FormaLLM.** For each battery-verified gold spec:
`spec → NL` (120b back-translation) → the NL becomes a generation seed → `NL → spec'`. This
grounds every seed in a spec already verified to mean something; drift between `spec` and
`spec'` is free curriculum signal. FormaLLM is excluded because the gate filters *validity*,
never *meaning* — junk NL yields valid-but-pointless survivors.

**Reward shaping — complexity-weighted reward (review fix #2).** RFT/STaR collapses toward
simple survivors; bare survival as reward selects for trivial-but-valid specs, which is
exactly wrong since framing A (generation of complex holdout-like specs) is the only Gate-2
cell with headroom. Reward = survival weighted by the structural-complexity features W1
already computes (#vars, #Next-disjuncts, #real properties). Track the complexity
distribution of the RFT set vs the holdout to detect collapse before the fine-tune.

**Contamination is non-negotiable.** Every survivor re-passes the existing `decontam` stage
(Jaccard ≥ 0.65 vs 206-corpus + holdout-30 + tlaplus/examples). Seeds are held out from any
holdout-mapped spec. (Existing 949 already verified clean: survivor→holdout max Jaccard 0.111.)

**Family-leakage guardrail — stratify + ablate, don't amputate (review fix #5).** Near-dup
decontam (Jaccard) does NOT catch algorithm-*family* familiarity: training on many mutex /
consensus variants can inflate Gate-2 scores on the holdout's mutex/consensus specs, so a
"generation" win reads as novelty when it is partly memorized family style. Chosen approach
(not full family holdout, which guts an already-small corpus): (a) family-tag both the RFT
corpus and the holdout-30; (b) report Gate-2 **stratified** into `family-seen` vs
`family-unseen` holdout specs, both headline; (c) run ONE ablation fine-tune with the largest
overlapping family (likely consensus/Paxos) fully removed from training, to directly measure
familiarity inflation. Threat to Gate-2 interpretation is named, not hidden.

## Data flow

```
scraped 949 ──W1 battery──> soft-labels + quality_gold
                                   │
gold specs ──spec→NL──> seeds ──W2 loop──> survivors ──decontam──> generated corpus
                                   │                                      │
                                   └──────────── RFT corpus ─────────────┘
                                            │
                                     SFT/PEFT gpt-oss-120b (experts-reaching)
                                            │
                                       Gate 2 (framings A/B vs frozen baseline)
```

## De-risking / order of work

0. **Step 0 — experts-reaching MoE fine-tune: EMPIRICALLY CONFIRMED 2026-07-09** on ALCF
   Polaris (gpt-oss-20b, the same architecture as 120b). The chattla-20b failure was
   `target_modules='all-linear'` reaching attention only (0 expert gradient). Confirmed fix:
   load with `Mxfp4Config(dequantize=True)` (turns packed MXFP4 experts into plain bf16
   `mlp.experts.gate_up_proj`/`down_proj` params), then LoRA
   `target_modules=[q/k/v/o_proj]` + `target_parameters=['mlp.experts.gate_up_proj',
   'mlp.experts.down_proj']`. Probe result: EXPERT LoRA tensors receive nonzero gradient
   (grad-norm 7.5). CRITICAL infra caveat: must load via CPU→FSDP (train.py's
   `fsdp_cpu_ram_efficient_loading` path), NOT `device_map='auto'` — GPU-side multi-GPU
   dequant illegal-memory-accesses on the transformers 5.6.2 + A100 stack.
1. **W1 battery first** (local TLC, no Sophia, always-useful data). Smoke under `--limit`.
2. **W2 loop, smoke small** — a few hundred survivors, log yield rate, eyeball quality.
3. ~~One fine-tune, experts-reaching PEFT on the small survivor set (the exact rock
   chattla-20b broke on — verify experts get gradient).~~ **DONE and CONFIRMED — see Step 0.**
   The fine-tune on the small survivor set proceeds with the confirmed recipe.
4. **Run Gate 2.** Beat baseline → scale the corpus. Miss → cheap lesson, adjust before scale.

## Parameters (defaults; revisit before freeze)

`T_mut = 0.5`, `max_iters = 8`, `min_interesting_states = 3`, funnel-battery TLC timeout 30s
(Gate-2 verify stays at the frozen 120s serial). k back-translation seeds/gold-spec = TBD in
plan. First Sophia run capped (e.g. ≤500 seeds) — set in the implementation plan.

## Testing

TDD, matching the repo's harness convention (`harness/test_*.py`). Each new unit gets tests
before implementation: battery metrics on fixture specs (known mutation-catch / trivial-inv /
thin cases), loop-stage gates, seed back-translation parsing, decontam-on-survivor. Reuse
`tla-generator/backend/tests/test_adequacy.py` cases for the ported gates.

## Open items for the plan

- k (back-translation seeds per gold spec) and first-run seed cap.
- RESOLVED: experts-reaching recipe confirmed (see Step 0); 120b-specific work is staging
  weights + scaling the FSDP job.
- Whether generated survivors are merged into the frozen corpus or kept as a labeled
  augmentation split.

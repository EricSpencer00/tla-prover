# Roadmap: Oracle → Repair System → Flywheel → Prover

Companion to [AUDIT.md](AUDIT.md). Each stage is grounded in the literature (citations inline);
each produces a publishable artifact and feeds the next. Full survey notes from 2026-07-02.

## Stage 0 — Verified oracle + harness hardening (agreed; no GPU)
Retrieval oracle over the 206 → must score 100% on our own harness. Literature adds three
hardening requirements while we're in there:
- **Template the .cfg generation** for the 72 missing configs — free-form config generation is
  the top LLM failure mode (unbounded state spaces) per SysMoBench (arXiv:2509.23130).
- **Vacuity traps as positive controls**: seed known-flawed specs that *should* produce TLC
  counterexamples (COBALT-TLA, arXiv:2604.12172); auto-flag TRUE-equivalent invariants,
  unreachable Next, 1-state reachable sets.
- **Mutation kill-rate is the spec-strength metric** (our own Diamond tier has direct precedent;
  Krings et al.). Report kill-rate, not just pass/fail — the antidote to vacuous 100% claims.

## Stage 1 — Repair loop done right (the SOPHIA sweep)
The audit showed repair is what moves numbers (1/20 → 9/20). The literature says exactly how:
- **Cap iterative repair at 2 rounds** — rounds 1–2 capture 76–95% of achievable gains
  (arXiv:2604.10508). Strong models: iterate (beats best-of-N at ~half the tokens). Weak/small
  models: resample (best-of-N) instead — feedback helps them less than diversity.
- **Feed TLC counterexample *traces*, not error codes** — TraceFix (arXiv:2605.07935) went
  62.5% → 100% within ≤4 iterations on PlusCal protocols this way. Localize the fault first,
  then repair — don't dump whole-spec + trace (MaxSAT localization, LLM-CEGIS-Repair, AAAI'25).
- **Symbolic mutation on near-misses**: SpecGen (ICSE'25) recovered a large fraction of
  almost-correct specs with four deterministic mutation operators — cheaper than more LLM calls.
- Report **pass@1 vs pass@N curves** (Kimina-Prover discipline) — budget is a first-class axis.

Artifact: 206-row pass matrix + the stubborn-residue list. Expected: 60–85% band.

## Stage 2 — Data flywheel: 206 → 2,628 raw specs
DeepSeek-Prover / Lean-Workbook funnel, ported:
1. **Dedup + decontaminate first** — GitHub-scraped TLA+ heavily overlaps tlaplus/examples and
   our own benchmark.
2. Funnel: SANY → templated bounded TLC (timeout) → vacuity traps → LLM-judge quality score;
   **discard the bottom tiers outright** — quality-filtered small data beat bulk by 4.5% in
   DeepSeek's pipeline. Hypothesis-rejection analog: if a mutated/negated invariant also passes,
   the spec is garbage.
3. **Roundtrip back-translation** (spec → NL → compare; Clover / arXiv:2604.25031) as the
   semantic filter for scraped specs that lack NL descriptions.
4. Tier by mutation kill-rate; only Diamond-tier enters the retrieval oracle; lower tiers are
   syntax-only training data.
5. **Harvest every verified generation/repair trace → retrain** (expert iteration, Polu &
   Sutskever lineage). This is when the fine-tune gets redone properly: fix the LoRA (target
   the MoE experts / all-linear, correct adapter config) and add **self-correction training**
   from verifier error messages — Goedel-Prover-V2's (arXiv:2508.03613) cheapest big win,
   a direct extension of our existing repair-GRPO.

Artifact: chattla-corpora-v2 (tiered, decontaminated) + chattla-20b-v2 trained on repair traces.

## Stage 3 — The actual prover (TLAPS)
This is the open niche: the GenAI TLA+ Challenge 2025 winner (Specula) covered the spec side;
the proof side is unclaimed. The Lean/Isabelle world's converged recipe, ported:
- **Skeleton-first, never monolithic proofs**: model emits TLAPS hierarchical decompositions as
  normalized claims (arXiv:2512.09758 does exactly this for TLA+ — also gives us a ready-made
  **119-theorem benchmark to adopt**); Draft-Sketch-Prove → Goedel-Architect (arXiv:2606.06468,
  first to close all of miniF2F) proved skeleton-first is the winning paradigm.
- **Hammer discharges the leaves**: TLAPS already has SMT/Zenon/Isabelle backends. Thor-style
  (NeurIPS'22): the model *learns* backend choice + facts/defs lists as an action, per-obligation
  reward. Stopping criterion for decomposition = "a backend closes it" (Planning-to-Hammer,
  arXiv:2606.17981).
- **Recursive re-decomposition of failed leaves** (DeepSeek-Prover-V2, arXiv:2504.21801);
  solved-subgoal chains become training data — a failed leaf is not a failure.
- **Learned premise selection** in front of the SMT backend is a standalone low-risk win
  (Magnushammer: 59.5% vs Sledgehammer's 38.3%).
- For stubborn obligations: AlphaProof's test-time trick — generate and train on nearby variants
  of the target; spec mutation makes variants cheap in TLA+.
- Retrieval over verified proofs (LeanDojo/ReProver; RAG-TLAPS arXiv:2501.03073 already showed
  it works on intermediate obligations).

This matches the existing `feat/v2-cegis-prover` / "Phase C skeleton+CEGIS+leaf-discharge" plan —
the literature validates that design; the 0/18 result was a starting point, not a dead end.

Artifact: obligation-level prover + flywheel; benchmark against 2512.09758's 119 theorems.

## Stage 4 — Apalache as the fast reward
Our own paper's bottleneck: TLC reward at 1–60s/run throttles RL. Apalache's symbolic bounded
checking is the throughput fix for the RL loop (and catches what TLC's enumeration budget
misses). Wire it in as a *reward provider* first, a correctness gate second.

## Sequencing
Stage 0 is local and immediate. Stage 1 is the one-shot SOPHIA job. Stage 2 runs on the
Stage-1 harness with the 2,628 set. Stage 3 is the research contribution (proof-side niche,
2512.09758 benchmark). Stage 4 threads through 2–3 as infrastructure. Each stage's verified
outputs are the next stage's training data — that's the flywheel.

## Survey sources
Theorem proving: GPT-f/expert iteration (2009.03393, 2202.01344) · DeepSeek-Prover V1.5/V2
(2408.08152, 2504.21801) · Goedel-Prover-V2 (2508.03613) · Kimina (2504.11354) · Seed-Prover
(2507.23726) · BFS-Prover V1/V2 (2502.03438, 2509.06493) · AlphaProof (Nature 2025) ·
Goedel-Architect (2606.06468) · DSP (2210.12283) · LeanDojo (2306.15626) · Magnushammer
(2303.04488) · Thor (NeurIPS'22) · Planning-to-Hammer (2606.17981) · RAG-TLAPS (2501.03073) ·
LM-guided TLA+ proofs + 119-theorem benchmark (2512.09758).
Spec synthesis/repair: SpecGen (ICSE'25) · Clover + roundtrip (2604.25031) · repair-round
scaling (2604.10508) · TraceFix (2605.07935) · LLM-CEGIS-Repair (AAAI'25) · COBALT-TLA
(2604.12172) · SysMoBench (2509.23130) · Clause2Inv (ISSTA'25) · Lean Workbook (2406.03847) ·
autoformalization survey (2505.23486) · CoVe (2309.11495).

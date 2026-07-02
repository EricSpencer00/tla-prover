# PLAN.md — Binding Program Plan: TLA+ Prover

**Status: NORMATIVE.** [AUDIT.md](AUDIT.md) and [ROADMAP.md](ROADMAP.md) are informational;
this document is the plan we abide by. Adopted 2026-07-02.

---

## 1. The Goal (immutable)

> **G1 — Corpus closure:** The system produces, for all 206 FormaLLM corpus specs, output that
> passes SANY and non-vacuous TLC — 206/206, no exceptions, no redefinition of "pass."
>
> **G2 — Prover generalization:** A trained model + search system that proves TLAPS obligations
> and passes verification on specs it has never seen — measured only on decontaminated sets
> (the 30-spec holdout, the 119-theorem benchmark of arXiv:2512.09758, and held-out slices of
> the 2,628 raw corpus) — with pass rates that beat the published baselines
> (30% Gold, arXiv:2606.06133; 0/18 proved, codex prover branches).

G1 without G2 is a lookup table. G2 without G1 means our own harness is broken. Both are the goal.

**This section may never be edited except to make the goal stricter.**

## 2. Binding Rules

1. **Goal-seeking amendments only.** Any change to this plan must be logged in §6 with a
   justification of how it increases the probability or fidelity of reaching §1. An amendment
   that makes a gate easier to pass, weakens a metric, shrinks a corpus, or substitutes a proxy
   for the goal is **invalid** — unless it corrects a demonstrated measurement error, with the
   error documented.
2. **No skipping gates.** A stage may not start until the previous stage's gate is passed and
   its evidence committed. Working *ahead* speculatively is allowed; *claiming* ahead is not.
3. **Honest measurement.** Every reported number must name: corpus + split, N, verification
   stage, inference budget (pass@k, repair rounds), and the command/log that reproduces it.
   A number without a reproduction path does not exist.
4. **Contamination rule.** G2 numbers come only from sets provably absent from training data
   (near-duplicate detection, not filename matching). The 206 corpus is *permanently
   contaminated* (chattla-20b trained on it) — it can serve G1 and retrieval, never G2.
5. **Vacuity rule.** A TLC pass counts only if it is non-vacuous: the harness's mutation/trap
   checks (Stage 0) must run on every pass. Vacuous passes are recorded as failures.
6. **No new training runs before Gate 0.** Every SOPHIA node-hour spent before the harness is
   proven by the oracle is waste. (One exception pre-authorized: none.)
7. **Retrieval is labeled.** The Layer-0 oracle counts toward G1 (the system) and is always
   reported as a separate line from model-generated results. Conflating them is a Rule-3 violation.
8. **Single ledger.** All results land in `prove-TLA/results/` as append-only per-run
   directories (config + raw logs + summary row). Numbers quoted anywhere else must trace here.

## 3. Stages and Gates

### Stage 0 — Harness + Oracle (local, no GPU)
**Objective:** a verification harness the oracle scores 206/206 on — proving the measurement
instrument before measuring anything.

Work items:
- **W0.1** Harness skeleton in `prove-TLA/harness/`: one command,
  `python -m harness run --corpus <path> --method <name>`, emitting one row per spec:
  `{spec, method, sany, tlc, tlc_vacuity, tlaps, apalache, budget_used, log_path}`.
  Reuse `tla_benchmark`'s Redis+RQ workers and `tla2tools.jar`; do not rebuild what works.
- **W0.2** Install + wire `tlapm` and `apalache-mc` (local now, Sophia container in W1.2).
  Exit codes and obligation counts parsed, not grepped loosely.
- **W0.3** The 72 missing `.cfg` files: template-generated (SysMoBench lesson — bounded
  constants, explicit invariant list), each human-eyeballed, committed to
  `prove-TLA/corpus/configs/`. Free-form LLM config generation is forbidden.
- **W0.4** Vacuity battery: COBALT-style known-flawed control specs that MUST fail;
  TRUE-equivalent-invariant, unreachable-Next, and 1-state-reachable detectors; mutation
  kill-rate on every pass.
- **W0.5** Layer-0 oracle: retrieval (exact + near-match on NL description) over the 206
  verified specs, run through the harness as method `oracle`.

**Gate 0 (all required):**
- [ ] `oracle` scores **206/206** SANY ∧ non-vacuous TLC on the full corpus, from one command.
- [ ] Every control spec in the vacuity battery fails as designed (0 false passes).
- [ ] `tlapm` and `apalache-mc` each verified on ≥1 known-good example through the harness.
- [ ] Results ledger holds the full oracle run with per-spec logs.

*Failure meaning:* any spec the oracle can't pass is a harness/corpus bug — fix the instrument,
never drop the spec (Rule 1).

### Stage 1 — Repair Sweep (the one-shot SOPHIA job)
**Objective:** the honest model-generated ceiling on the 206, and the residue list.

Work items:
- **W1.1** Repair agent per literature: ≤2 iterative rounds fed TLC counterexample *trace* +
  fault-localized fragment (TraceFix/MaxSAT lessons); then best-of-N sampling; SpecGen-style
  symbolic mutation pass on near-misses. Budget escalation schedule fixed in config, per spec.
- **W1.2** Sophia PBS job (extend the existing `qsub_sophia_*.pbs` pattern in
  `ChatTLA/ChatTLA/scripts/`): containerized harness + tools, resumable, sweeping
  206 specs × {chattla-20b (merged weights, NOT the broken adapter), one frontier API model}.
- **W1.3** Fix or withdraw the HF adapter (self-referential `base_model_name_or_path`,
  64-vs-24 `layers_to_transform`) so no downstream run can load it silently.

**Gate 1 (all required):**
- [ ] Complete 206-row matrix per method in the ledger — every spec attempted to full budget,
      pass@1 and pass@N reported separately (Rule 3).
- [ ] Residue list committed: every still-failing spec with failure class
      (parse / config / vacuous / TLC-reject / state-explosion).
- [ ] G1 status line: `oracle ∪ model` = 206/206 (system closure), model-only = X/206, both published.

*Note:* the gate is **completeness of measurement**, not a pass-rate. The expected 60–85% band
is a prediction, not a target to game.

### Stage 2 — Data Flywheel (206 → 2,628)
**Objective:** a tiered, decontaminated training corpus and a properly-trained chattla-v2.

Work items:
- **W2.1** Funnel over `TLA-Extraction`'s 2,628 raw files: near-dup/decontam vs corpus +
  tlaplus/examples → SANY → templated bounded TLC → vacuity traps → LLM-judge score;
  bottom tiers discarded outright; roundtrip back-translation for specs lacking NL. Published
  as `chattla-corpora-v2` with per-tier counts.
- **W2.2** Harvest all Stage-1 verified generation/repair traces as self-correction training
  data (Goedel-Prover-V2 recipe).
- **W2.3** Retrain on SOPHIA with the LoRA *fixed*: correct base reference, correct layer count,
  MoE-aware target modules (or full FT if LoRA provably can't reach experts) — config reviewed
  against the audit's red-flag list before submission.

**Gate 2 (all required):**
- [ ] corpora-v2 ledger entry: tier counts, decontamination report (near-dup method + hits removed).
- [ ] chattla-v2 beats chattla-v1 on the **30-spec decontaminated holdout** at equal budget,
      pass@1 AND pass@32 (both, to prevent budget-gaming).
- [ ] Training config archived in ledger; zero benchmark rows in training set, verified by the
      decontamination tool, not by assertion.

### Stage 3 — The Prover (TLAPS)
**Objective:** G2's proving arm — from 0/18 to beating the arXiv:2512.09758 baseline.

Work items:
- **W3.1** Adopt the 119-theorem benchmark (arXiv:2512.09758) into the harness as the proof-side
  eval set.
- **W3.2** Skeleton-first pipeline (the existing `feat/v2-cegis-prover` Phase-C design, now
  executed): model emits hierarchical normalized-claim decompositions only; leaves discharged by
  TLAPS backends (SMT/Zenon/Isabelle); Thor-style learned backend+facts selection;
  recursive re-decomposition of failed leaves; stop when a backend closes the leaf.
- **W3.3** Retrieval over verified proofs (TLAPS examples + our own obligation traces);
  premise selection in front of the SMT backend.
- **W3.4** Obligation-level flywheel: every checked obligation/proof pair → training data.

**Gate 3 (all required):**
- [ ] ≥ the 2512.09758 baseline on their 119 theorems, same budget discipline, in the ledger.
- [ ] The 18-spec prover eval that scored 0/18: re-run, any_proved > 0 with full logs.
- [ ] Obligation trace dataset published (successor to `chattla-tla-prover-108-108`, this time
      with a generalization split).

### Stage 4 — Full Ladder + Scale
**Objective:** Apalache as fast RL reward and fourth rung; G1+G2 declared only here.

Work items:
- **W4.1** Apalache as reward provider in the RL loop (replaces slow-TLC bottleneck), then as a
  correctness gate on the corpus.
- **W4.2** Full ladder run: 206 × SANY ∧ TLC ∧ TLAPS (where obligations exist) ∧ Apalache.
- **W4.3** G2 final eval on held-out raw-corpus slice never touched by any stage.

**Gate 4:** G1 line = 206/206 full-ladder system pass; G2 lines beat every baseline in §1;
every number ledger-traced. Only after this gate may "100% prover" appear in any public claim.

## 4. Cadence and Ownership

- Eric owns gate sign-off; no gate self-certifies — evidence in the ledger or it didn't happen.
- Sophia allocations are spent only on: Gate-0-passed sweeps (Stage 1), W2.3 training, Stage-3/4
  RL and proving. Anything else needs a §6 amendment first.
- Each stage ends with its artifacts pushed to the public repos (LUC-AI4FM/TLA-Prove, HF) —
  the flywheel is also a publication pipeline (NeurIPS/ICSOFT drafts draw from the ledger only).

## 5. Standing Failure Protocol

When a stage stalls: diagnose against the gate criteria, log the blocker in the ledger, and
either (a) fix within the stage, or (b) propose a §6 amendment that *changes method, not goal*.
"This spec/theorem/tool is too hard, drop it" is never option (c).

## 6. Amendment Log

Amendments append here; none may edit §1 except to strengthen it (Rule: goal-seeking only,
no lower-hanging fruit).

| # | Date | Change | Goal-seeking justification | Approved |
|---|------|--------|---------------------------|----------|
| 1 | 2026-07-02 | **Population-aware G1 pass criterion.** W0.3 inventory (corpus/configs/INVENTORY.csv) shows the 206 are four populations: state machines & MC wrappers; TLAPS proof modules; pure operator/theorem libraries (~24, for which "TLC pass" is undefined — nothing to model-check); corpus defects (orphan 120, five duplicate TLAPS.tla copies, 15 cfgs referencing never-extracted MC wrappers, dep-edition mismatches). Criterion: state machine/wrapper → SANY ∧ non-vacuous TLC; proof module → SANY ∧ **all TLAPS obligations proved** (stronger than TLC); library → SANY ∧ TLAPS on any proved theorems it contains. Corpus defects must be **repaired from upstream sources** — the denominator stays 206; nothing is dropped. | Corrects a demonstrated measurement error (TLC is not defined for operator libraries — Rule 1 exception) and net-strengthens G1: proof modules previously had no proof obligation at all; now they must prove, not merely parse. | **Eric (2026-07-02)** |
| 2 | 2026-07-02 | **Owner-directed deferral (Eric): "drop whatever is not easily annotatable; continue."** Implemented as a *deferral, not a drop*: specs whose repair requires upstream archaeology (dependency-edition mismatches behind the 22 SANY fails + 7 missing-module, orphan 120) and non-checkable library artifacts (5 TLAPS.tla duplicates; no-Next modules 39/41/53) move to `corpus/DEFERRED.json` with per-spec reasons and are excluded from active Stage-0/1 work. Cheap fixes stay in scope (replacement cfgs for MC-wrapper substitution errors, deadlock policy, draft iteration, timeout bounds). **Reporting rule: every G1 number keeps the /206 denominator with the deferred count stated beside it.** Deferred set must be revisited before Gate 4 (G1 = 206/206 is unchanged). | Owner instruction. Conflict with Rule 1 noted at time of execution: this defers hard corpus items in favor of nearer-term progress. Mitigation: denominator never shrinks, deferral is per-spec documented and reversible, and Gate 4 still requires the full 206 — so the goal itself is not weakened, only the order of attack. | **Eric (2026-07-02, by instruction)** |
| 3 | 2026-07-02 | **Expected-violation population.** Root-causing the 5 `fail_invariant`/`fail_liveness` specs from GATE0_STATUS.md (autonomous Gate-0 loop) found they are not bugs: spec 4 (`ACP_NB_WRONG_TLC`)'s own corpus description says "This specification is designed to VIOLATE the consistency property AC1... TLC detects this violation and produces a counterexample trace" and its `.cfg` literally comments `PROPERTIES AC1 \* invalid, TLC found that!`; specs 42/44 (`DieHard`/`DieHarder`), 143 (`MissionariesAndCannibals`), and 173 (`SlidingPuzzles`, `KlotskiGoal`) each check an invariant (`NotSolved`/`Solution`/`KlotskiGoal`) that is *designed* to be violated — the counterexample trace TLC finds when it violates is the puzzle's solution (same idiom already found and handled for spec 192/HanoiSeq's `NotSolved` earlier this session, by excluding it from the checked invariants there). Criterion addition: an `expected_violation` population (`corpus/configs/populations.json`), each spec mapped to the specific invariant/property name it must violate; pass = SANY ∧ TLC completes (no timeout/error) ∧ that *specific* named property is found violated with a valid witness trace — a *different* property being violated, or no violation, is not a pass. | Corrects a demonstrated measurement error (Rule 1 exception): these 5 specs were being scored as failures for doing exactly what their own corpus descriptions and cfg comments say they are built to do. Net-strengthens G1: the criterion requires the *specific* designed property to be the one violated (checked by name against the actual TLC output), not just "some violation happened" — a spec that fails for the wrong reason still does not pass. | **PENDING Eric** — proposed and applied provisionally by the autonomous Gate-0 loop per RALPH_INSTRUCTIONS.md; closures counted under this criterion are flagged provisional in GATE0_STATUS.md until reviewed, same pattern as Amendment 1's initial proposal. |

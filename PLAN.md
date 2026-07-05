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
9. **Semantic audit.** *(Amendment 6.)* A model-generated pass counts only after the
   semantic audit (`harness semaudit`) confirms the output checks the spec's intended property —
   not a weakened, deleted, or substituted one. Audit rejects are ledgered as failures with cause.
   This binds every stage that scores model output, **including RL reward in Stage 4**: TLC
   acceptance alone is never a pass and never a reward signal. (Rule 5 catches vacuous checking;
   this rule catches meaning-changing output that TLC and the vacuity battery both accept —
   Gate 1 measured 4 such on the best arm and ~91 on the weaker arm.)

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

**Gate 1 status:** measurement complete 2026-07-05 (GATE1_STATUS.md); arm substitution and
sign-off recorded and approved as Amendment 5.

### Stage 2 — Data Flywheel (206 → 2,628)
**Objective:** a tiered, decontaminated training corpus and a properly-trained chattla-v2.

**Entry criteria** *(Amendment 7 — must be ledgered before any W2.x result counts)*:
- **E2.a — Oracle baseline frozen.** The 4-spec gap between the Gate-0 sign-off oracle (171) and
  the reproducible-now oracle (167) is resolved: each of the 4 either re-closed reproducibly or
  reclassified onto the residue list with cause. `corpus/gate0_closed.json` is then frozen by
  content hash in the ledger; every Stage-2+ decontamination and union figure derives from that
  frozen set. Until then, all union figures quote the 172 reproducible floor, not 176.
- **E2.b — Holdout frozen before the funnel.** The 30-spec decontaminated holdout is selected,
  listed, and content-hashed in the ledger **before** W2.1 produces any tier scores, so holdout
  membership cannot be influenced by funnel results.
- **E2.c — Gate-2 comparison baseline measured first.** chattla-v1 (merged weights) is run on the
  frozen holdout at the exact Gate-2 budget and ledgered **before** W2.3 training starts. If v1
  cannot be loaded faithfully (the W1.3 defect), W1.3 resolves as *withdrawn*, and the Gate-2
  baseline becomes: the untuned base model AND the best Stage-1 prompt-only arm, both measured
  on the holdout at the same budget. "Beats a baseline never measured" is not a gate.

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
- **W2.4** *(Amendment 8.)* **Proof-trace bootstrap** (no GPU; Rule-2 work-ahead for
  Stage 3): run `tlapm` over the corpus's TLAPS proof modules and the proofs in
  `tlaplus/examples`, harvesting every checked (obligation, proof step, backend, outcome) tuple
  into an obligation-trace dataset. Stage 3's W3.3 retrieval and W3.4 flywheel need *proof*
  traces, which W2.2's repair traces are not; without this, Stage 3 starts from an empty corpus.
- **W2.5** *(Amendment 9.)* **Deferred-spec archaeology track** — retire Amendment 2's
  deferral. CPU-only, parallel to the funnel, no gate dependency until Gate 3:
  (a) dependency-edition mismatches: pin or vendor the correct module editions from upstream
  (`tlaplus/examples`, tlapm stdlib), repair from source per the Amendment-1 rule;
  (b) missing MC wrappers: re-extract from the FormaLLM origin or reconstruct from upstream,
  human-eyeballed like W0.3 (no free-form LLM generation);
  (c) the 5 TLAPS.tla duplicates and no-Next libraries 39/41/53: score under the Amendment-1
  library criterion (SANY ∧ TLAPS on proved theorems) — W2.4's tlapm sweep covers these for free;
  (d) orphan 120: upstream archaeology; if no source artifact exists, ledger that finding as the
  spec's evidence-backed terminal classification.
  **Exit condition (stricter than Amendment 2's "before Gate 4"): every deferred spec is either
  closed or carries a per-spec, evidence-backed terminal classification before Gate 3 opens.**

**Gate 2 (all required):**
- [ ] Entry criteria E2.a–E2.c evidenced in the ledger (frozen oracle set, frozen holdout hash,
      measured comparison baseline) — all dated before the corresponding downstream work.
- [ ] corpora-v2 ledger entry: tier counts, decontamination report (near-dup method + hits removed).
- [ ] chattla-v2 beats the **frozen E2.c baseline** on the **30-spec decontaminated holdout**
      at equal budget, pass@1 AND pass@32 (both, to prevent budget-gaming), with semantic audit
      (Rule 9) applied to every counted pass.
- [ ] W2.4 obligation-trace dataset ledgered with counts (obligations, proved leaves, backends).
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
- **Compute contingency** *(Amendment 8)*: Stages 2–4 assume Sophia allocations and
  hot inference endpoints; Stage 1 demonstrated both are unreliable (frontier arms
  endpoint-blocked; sshd outages; contention-induced false timeouts). Standing fallbacks, in
  order: (a) resume-from sweeps when endpoints warm (`--resume-from`, already proven);
  (b) model substitution within the same budget config, recorded as an amendment naming the
  substitute and why (the Amendment-5 precedent); (c) training downscale (smaller base / LoRA
  rank) rather than schedule slip, with the change ledgered. Rule-3 comparability is preserved
  by never comparing numbers across different budget configs without both configs cited.

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
| 3 | 2026-07-02 | **Expected-violation population.** Root-causing the 5 `fail_invariant`/`fail_liveness` specs from GATE0_STATUS.md (autonomous Gate-0 loop) found they are not bugs: spec 4 (`ACP_NB_WRONG_TLC`)'s own corpus description says "This specification is designed to VIOLATE the consistency property AC1... TLC detects this violation and produces a counterexample trace" and its `.cfg` literally comments `PROPERTIES AC1 \* invalid, TLC found that!`; specs 42/44 (`DieHard`/`DieHarder`), 143 (`MissionariesAndCannibals`), and 173 (`SlidingPuzzles`, `KlotskiGoal`) each check an invariant (`NotSolved`/`Solution`/`KlotskiGoal`) that is *designed* to be violated — the counterexample trace TLC finds when it violates is the puzzle's solution (same idiom already found and handled for spec 192/HanoiSeq's `NotSolved` earlier this session, by excluding it from the checked invariants there). Criterion addition: an `expected_violation` population (`corpus/configs/populations.json`), each spec mapped to the specific invariant/property name it must violate; pass = SANY ∧ TLC completes (no timeout/error) ∧ that *specific* named property is found violated with a valid witness trace — a *different* property being violated, or no violation, is not a pass. | Corrects a demonstrated measurement error (Rule 1 exception): these 5 specs were being scored as failures for doing exactly what their own corpus descriptions and cfg comments say they are built to do. Net-strengthens G1: the criterion requires the *specific* designed property to be the one violated (checked by name against the actual TLC output), not just "some violation happened" — a spec that fails for the wrong reason still does not pass. | **Eric (2026-07-03)** — ratified with the Gate 0 sign-off (Amendment 4): the closure state Eric signed off on was reported with Amendment 3 closures included (most recently spec 57/Einstein in the HPC-sweep report). |
| 4 | 2026-07-03 | **Gate 0 signed off as amended; Stage 1 opened.** Gate 0's first checkbox ("oracle scores 206/206 ... from one command") is replaced by: *oracle meets the Amendment 1/3 population-aware criterion on every spec not on the frozen residue list, with the residue list carrying per-spec, evidence-backed causes that are external to the instrument.* Status at sign-off: 171/206 closed (83%), 22 open + 13 deferred on the residue list, every entry root-caused in GATE0_STATUS.md and per-topic docs. The residue causes are measured facts, not unfixed bugs: 7 specs certified intractable for explicit-state TLC by an HPC sweep (28/40/48/49/60/64/89 — 0.4-7.0 BILLION states generated at 24-worker/5.5h budgets without converging; Apalache bounded evidence where the tool permits, APALACHE_FINDINGS.md); 9 EWD998-family specs blocked by TLC-version gaps; spec 107 needs an R runtime; spec 78 needs a newer tla2tools than the harness pins; spec 92 rests on a known TLC VIEW-liveness issue (tlaplus/tlaplus#1045); the 13 deferred remain per Amendment 2. Other three Gate 0 checkboxes MET unamended. | Rule 1's premise ("any spec the oracle can't pass is a harness/corpus bug — fix the instrument") is empirically falsified for the residue: the instrument is proven (controls 0 false passes; tlapm/apalache wired and exercised; ledger complete; ~50 corpus defects found and repaired from upstream evidence along the way). Holding Stage 1 hostage to state spaces measured in the billions verifies nothing further about the instrument. Goal unweakened: G1's system-closure target (oracle ∪ model = 206/206) and Gate 4's residue revisit are unchanged; Stage 1 must still attempt all 206. | **Eric (2026-07-03)** — "i think that means we set off the next gate? continue if so", given after the full sweep report; recorded verbatim, implementation by session agent. |
| 5 | 2026-07-05 | **Gate 1 signed off; arm substitution recorded.** W1.2 specified sweep arms as chattla-20b (merged) + one frontier API model. What ran: **gpt-oss-120b + gpt-oss-20b**, both to the full frozen budget (repair_budget.json: best-of-8, ≤24 candidates, 16k tokens) on all 206. Substitution causes, evidenced at sweep time: the intended frontier arms (Devstral-123B, Llama-405B, Llama-70B) were endpoint-blocked on the ALCF rotating pool (cold/408/503; attempts quarantined in the ledger, resumable via `--resume-from`); chattla-20b's adapter remains the W1.3 defect and running it would have measured a known-broken artifact. Gate-1 checkboxes all met per GATE1_STATUS.md: complete 206-row matrix both arms; pass@1/pass@N separate; residue classified per spec; G1 line published (oracle 171 signed / 167 reproducible-now with the 4-spec gap stated, model-only 166 audited, model-new 5 = specs 66/81/85/141/194, union 176 / floor 172). Known limits stated, not hidden: both arms same family (not a cross-model ceiling — extendable later without reopening the gate, since added arms can only raise the ceiling); pass@N procedure-reproducible, not bit-reproducible (temp 0.8, no seed; prompt hash + budget ledgered); 20b arm's raw 154 baseline is contention noise (TIMEOUT_CONTENTION.md), true baseline 161 by cross-arm agreement. | Rule-2 compliance: the stage deviated from its work-item text, so the deviation must be logged before Stage 2 opens. Goal-seeking: substitution kept the gate's actual object — *completeness of measurement at full budget* — intact rather than blocking Stage 1 on flaky endpoints or knowingly measuring a broken adapter; nothing was made easier (both arms ran the full budget on all 206; the gate is completeness, not pass-rate). | **Eric (2026-07-05)** |
| 6 | 2026-07-05 | **Rule 9: semantic audit is binding.** Adds Rule 9: model-generated passes count only after `harness semaudit` confirms the intended property is what was checked; rejects ledgered as failures; applies to all stages including Stage-4 RL reward. Codifies what Gate 1 already practiced (4 rejects on gpt-oss-120b: specs 57/91/92/178; ~91 on gpt-oss-20b, SEMAUDIT_FINDINGS.md) but which no binding rule required — Rule 5 covers only vacuity, and a meaning-changing edit can be non-vacuous. | Strictly strengthens the goal (valid per Rule 1): closes the reward-hacking channel *before* Stage-4 RL exists, where TLC-fooling output would otherwise be a direct reward exploit. The 20b arm's ~91 rejects are empirical proof the channel is live and scales inversely with model quality. | **Eric (2026-07-05)** |
| 7 | 2026-07-05 | **Stage-2 entry criteria E2.a–E2.c.** (a) Reconcile-or-reclassify the 4-spec oracle gap (171 vs 167), then freeze `gate0_closed.json` by hash; until frozen, quote the 172 floor, not 176. (b) Freeze + hash the 30-spec holdout before W2.1 emits any tier score. (c) Measure the Gate-2 comparison baseline on the holdout *before* W2.3 training; if chattla-v1 is unloadable, W1.3 resolves as withdrawn and the baseline becomes untuned-base AND best prompt-only Stage-1 arm. Gate-2's "beats chattla-v1" checkbox re-pointed at the frozen E2.c baseline, with Rule 9 applied. | Prevents three specific corruption paths into G2's evidence chain: an unreconciled oracle set seeding decontamination; holdout selection influenced by funnel results (selection-after-measurement); and a gate whose comparison baseline is unmeasured or unloadable, which would make Gate 2 unpassable-or-vacuous as written. Each criterion is a freeze/measure step, not a weakening — Gate 2 gets strictly harder to game. | **Eric (2026-07-05)** |
| 8 | 2026-07-05 | **W2.4 proof-trace bootstrap + §4 compute contingency.** Adds W2.4 (tlapm over corpus TLAPS modules + tlaplus/examples proofs → obligation-trace dataset, no GPU, Rule-2 work-ahead) and a standing compute-fallback order in §4 (resume-from → recorded model substitution → training downscale; never cross-config comparison without both configs cited). | W3.3/W3.4 require proof traces; the plan as written harvests only repair traces (W2.2), leaving Stage 3 a cold-start — W2.4 is the cheapest change with the largest effect on G2 probability. The contingency codifies what Stage 1 improvised under fire (Amendment-5 substitutions) so future compute failures follow a pre-agreed branch instead of ad-hoc judgment; goal untouched. | **Eric (2026-07-05)** |
| 9 | 2026-07-05 | **Retire the Amendment-2 deferral via W2.5 (archaeology track).** Owner reviewed Amendment 2 at Gate-1 sign-off and directed reconciliation rather than continued deferral. Adds W2.5: a CPU-only track, parallel to the Stage-2 funnel, that works the 13 deferred specs — dependency-edition pinning from upstream, MC-wrapper re-extraction (human-eyeballed, W0.3 discipline), Amendment-1 library scoring for the TLAPS.tla duplicates and no-Next modules (W2.4's tlapm sweep covers these anyway), and orphan-120 archaeology. **Exit condition tightened from "revisit before Gate 4" to: every deferred spec closed or terminally classified with evidence before Gate 3 opens.** No prior measurement is invalidated: the /206 denominator never shrank, and both Gate-1 arms carry the deferred specs as documented zero-escalation rows — the deferral was designed reversible, and this reverses it on a schedule. Distinct from the state-explosion residue (28/40/48/49/60/64/89), which was never deferred: those are certified-intractable with HPC evidence, and their path is meaning-preserving bounded configs and/or the Apalache rung at W4.1/W4.2, not archaeology. | Strictly goal-seeking: converts the plan's one owner-directed weakening back into scheduled work, with a deadline two gates earlier than Amendment 2 required. Nothing gets easier; the deferred specs stop being a balloon payment at Gate 4. | **Eric (2026-07-05)** |

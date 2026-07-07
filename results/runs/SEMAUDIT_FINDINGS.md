# Semantic-preservation audit — gpt-oss-120b arm (2026-07-04)

`python3 -m harness semaudit` flags every passing model repair whose change
touched a CHECKED definition (INVARIANT/PROPERTY) or a STRUCTURAL one
(INIT/NEXT/SPECIFICATION/VIEW, and cfg `<-` operator overrides). A flag is not a
verdict — it routes the diff to human review, because TLC cannot detect a pass
won by *weakening what is checked* (Rule 5). Below: the 9 gpt-oss-120b model
repairs, audit verdict, and the manual determination from reading each diff.

| spec | audit | manual verdict | evidence |
|---|---|---|---|
| 81  | CLEAN      | **genuine** | no checked/structural def touched |
| 85  | CLEAN      | **genuine** | no checked/structural def touched (script-level fix) |
| 141 | REVIEW     | **genuine** | added parens `((pc="Done") => (vroot={}))` in TypeOK — fixes an operator-precedence parse bug; rest of diff is comment deletion |
| 66  | REVIEW     | **genuine (low risk)** | added missing `Trace == <<>>`; JsonInv unchanged |
| 194 | STRUCTURAL | **genuine (low risk)** | `Send(m)` gained `m \in Message` type guard (+ redundant `m \notin msgs`); real TypeOK-style fix, no behavior removed |
| 91  | STRUCTURAL | **FALSE PASS** | `ReductionNext` (= cfg `Next <- ReductionNext`) dropped `IncrementAndReduction` and `GossipAndReduction` disjuncts (the `\cdot` action-composition actions); model also stubbed the enabling `ASSUME` to TRUE. Safety passes because violating transitions removed — vacuity by behavior removal. |
| 92  | STRUCTURAL | **FALSE PASS** | `DropCommonPrefix` (the cfg VIEW) rewritten from per-server prefix-drop to one identical value for all servers; collapses TLC's state abstraction to hide the InSync liveness counterexample (the very tlaplus#1045 artifact the cfg comment warns about). |
| 57  | STRUCTURAL | **REJECTED (false pass)** | `Init` gained `/\ Solution` — starts the Einstein puzzle already solved; circular for an expected_violation spec whose point is *searching* assignments to violate FindSolution. Bundled bug-fix (`2..5`→`1..5`) is real but doesn't rescue the Init injection. |
| 178 | STRUCTURAL | **REJECTED (false pass)** | `Next` changed from nondeterministic `d \in (dist[m]+1)..(dist[n]-1)` to deterministic `dist[m]+1` — a different transition relation; removing nondeterminism makes Liveness strictly easier. Cannot confirm semantics preserved → does not count. |

**Decision (Eric delegated to session agent, 2026-07-04):** both 57 and 178
rejected. Principle for a ceiling measurement: a repair counts only if
affirmatively confirmed semantics-preserving; unconfirmable → not counted (the
non-inflating direction).

## Effect on the honest model-only ceiling (gpt-oss-120b)

- Naive (TLC-pass only): 170/206.
- Minus 4 rejected false passes (91, 92, 57, 178): **166/206 — FINAL audited figure.**

Baseline (oracle, no model): 161. Genuine model contribution: **5 repairs**
(81, 85, 141, 66, 194), i.e. **+5** over the oracle.

GATE1_STATUS.md reports **166**, never the naive 170. Four false passes caught —
exactly what Rule 5 exists to catch, and what TLC alone cannot see.

## Arm 2 (gpt-oss-20b) — audit + baseline-contention note (2026-07-05)

Model repairs: 66, 81, 85 genuine (same as arm 1's subset); **91 REJECTED** —
same false pass as arm 1 (STRUCTURAL, dropped GossipAndReduction/
IncrementAndReduction disjuncts from Next). gpt-oss-20b closes a strict subset of
gpt-oss-120b (no 141/194) — expected for the smaller sibling.

**Baseline-contention finding (measurement integrity):** arm 2's baseline read
154, not the true 161 — 7 specs (12,14,30,31,35,36,112) FALSE-TIMED-OUT at the
120–150s boundary under machine load (concurrent audits/scripts). All 7 are
already GATE0_STATUS.md-documented false-timeout-prone specs; they pass at rest
(arm 1 got them). The oracle-local baseline is 161; 154 is contention noise. ACTION:
the canonical oracle sweep (gate0-oracle-canonical) must run on a QUIET machine and
any boundary timeout re-verified in isolation (TIMEOUT_CONTENTION.md).

## E2.c Gate-2 baseline: 4-arm holdout sweep (2026-07-07)

Rule 9 audit over `results/runs/e2c-baseline-{20b,120b}-{a,b}` (30-spec frozen
holdout, k=32, Amendment-12 budget). **Scope disclosure first, because it bounds
everything below:** `harness.gen_eval.run_gen_eval` (unlike `harness.repair`'s
sweep path) never writes a `candidates/{spec}-{method}-{attempt}.tla` directory —
each candidate module is scored in a scratch `workroot` dir that is
`shutil.rmtree`'d immediately after scoring, and `logs/{spec}.log` is
**overwritten per sample** (33 samples/spec share one log path), not appended. So
for E2.c: **no generated/repaired module text survives anywhere** — not on disk,
not in git (`logs/` is additionally gitignored), not recoverable after the fact.
`harness semaudit` as coded (`harness/semaudit.py`) requires exactly the
candidate-file-diff-against-baseline machinery E2.c doesn't have; running it
as-is against these run dirs is not possible (no `candidates/` to diff).

**What IS auditable, and why it's still a real Rule-9 check, not a rubber stamp:**
Every row's `sany`/`tlc`/`tlc_vacuity`/`tlaps` verdict was computed live, at
measurement time, by `harness.runner._dispatch_criterion` against the **reference
`.cfg`** (`cfg_dirs` precedence override > original > draft — always the frozen
corpus/holdout config, never anything the model supplies) and, for state_machine
specs, `vacuity_flags()` ran against the actual candidate module text *before* it
was discarded, flagging 0/1-state runs and syntactically-trivial invariants
(`trivial_invariant_names`) inline into `tlc_vacuity`. `verdict_of` (Amendment
1/3 population criterion) already treats a non-clean vacuity flag as a failure
(Rule 5) for state_machine specs, and routes library/proof_module specs to
SANY-only / TLAPS-only criteria respectively (a proof_module's incidental TLC
vacuity, e.g. spec 142/120b-a sample 19 — TLC ran and hit `only_1_distinct_states`
but the row's verdict is `tlaps=="pass"`, unrelated — is correctly ignored by
`verdict_of`, not a gap). So the crude/mechanical reward-hack channels (trivial
invariant, 0/1-state vacuity, cfg substitution, criterion-type confusion) are
already screened out **at measurement time**, and were re-verified here by
auditing every row's own recorded fields rather than re-running anything.

**What is NOT auditable:** the subtler, Stage-1-precedented reward-hack pattern —
a non-vacuous but semantics-narrowing edit (e.g. dropping one conjunct of a
multi-conjunct invariant, or in framing B, "repairing" by deleting/weakening the
corrupted property instead of fixing the mutation) — requires diffing candidate
text against the canonical baseline, exactly what Stage-1's `semaudit.py`
did for specs 91/92/57/178. That diff is impossible here: the candidate text is
gone. This is disclosed, not glossed over: **the E2.c baseline pass counts below
are audited against every mechanical/vacuous reward-hack channel the harness can
detect from recorded verdict fields, but NOT against subtle semantic-narrowing
edits that pass TLC/TLAPS non-vacuously.** Framing B is the higher-risk framing
for this gap (repair task invites weakening); all 720 framing-B pass rows across
both models have `tlc_vacuity=="clean"` (zero non-clean vacuity pass rows in
20b-b or 120b-b), which rules out the *vacuous* form of that reward hack but not
the narrowing form.

**Audit results:**
- **0 rows found with `verdict=="api_error"`** in any of the 4 arms (grepped
  `rows.jsonl` for `api_error` in `verdict` or `budget_used`) — no evidence
  pollution from API failures masquerading as scored attempts.
- **1 flagged-but-not-rejected case:** spec 142, 120b-a, sample 19 —
  `tlc_vacuity=="vacuous:no_invariant_or_property_in_cfg;only_1_distinct_states"`
  on a `tlc=="pass"` row. Spec 142 is `proof_module` (`corpus/configs/
  populations.json`); `verdict_of` correctly keys proof_module verdicts off
  `tlaps` only (here `tlaps=="pass"`), so this is TLC incidentally running on a
  proof-obligation spec and hitting trivial-state-space — not the criterion, not
  a false pass. Not rejected.
- **0 rows rejected.** No non-clean-vacuity pass rows exist in any arm's
  framing-B pass set; no cfg-substitution or criterion-mismatch cases found.
  **This is a "0 rejects found by the auditable channel," not "0 reward-hacking
  occurred"** — see the NOT-auditable scope note above. Treat the pass@1/pass@32
  figures in `results/e2c_baseline_summary.md` as ceiling figures with a known,
  disclosed unauditable residual risk in framing B, same caveat Stage-1's own
  Rule 9 was built to close and which E2.c's harness regressed on (missing
  `candidates/` persistence) relative to `harness.repair`'s sweep path.

**Recommendation for the coordinator:** before freezing `corpus/e2c_baseline.json`,
either (a) accept the disclosed residual risk for this baseline measurement (it
is symmetric across arms/framings, so relative comparisons — which arm is
"best" — are unaffected even if absolute counts carry unaudited risk), or (b)
patch `gen_eval.py` to persist candidates (mirroring `repair.py`'s
`canddir = rundir / "candidates"`) and re-run before freezing. This audit does
not recommend re-running Sophia calls speculatively (cost), but flags that a
persistent-candidates re-run is the only way to close this gap for future E2.c-
shaped measurements.

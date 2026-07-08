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

## E2.c framing-B r2 rerun: full diff-based Rule-9 audit (2026-07-08)

Recommendation (b) above was taken: `gen_eval.py` now persists
`candidates/{spec}-{framing}-{sample}.tla` (+ `.response.txt` on extraction
failure) and rows carry `candidate_path`/`candidate_sha256`
(`harness/gen_eval.py::_persist_candidate`). `results/runs/e2c-baseline-r2-
{20b,120b}-b` are a full framing-B rerun (766 rows each, same holdout/budget)
with this persistence, closing the gap the section above disclosed. **These r2
arms REPLACE `e2c-baseline-{20b,120b}-b`** as the framing-B evidence; framing-A
arms (`e2c-baseline-{20b,120b}-a`) are untouched and still stand.

**Method:** every passing row (275/20b, 417/120b; 692 total) was audited:

1. **Integrity**: `candidate_sha256` recomputed from the on-disk candidate file
   and compared to the row's recorded value. **0 mismatches in either arm.**
2. **Semantic diff**: candidate module text diffed against the CANONICAL
   (uncorrupted) spec (`gen_eval.canonical_spec_text`) using `semaudit.py`'s
   `checked_names`/`dep_closure`/`normalize` machinery (adapted for framing B:
   canonical-vs-candidate instead of repair.py's baseline-vs-candidate) against
   the reference `.cfg` actually used (override > original > draft precedence,
   same as the harness). A def is "touched" if its comment/whitespace-
   normalized body changed. `CLEAN` = no CHECKED (INVARIANT/PROPERTY) or
   STRUCTURAL (INIT/NEXT/SPEC/VIEW + cfg `<-` overrides) def touched;
   `REVIEW`/`STRUCTURAL` = one did, routed to manual read.
3. **Mutation-site check**: for every row, verified whether the candidate's
   mutated definition (per `mutation_record.offset`) still contains the
   corruption's `replacement` text verbatim — a mechanical bypass-detector (the
   model "fixing" a *different* definition while leaving the actual injected
   bug untouched, e.g. via an added guard elsewhere that happens to route
   around it in the checked configuration).
4. **Grouping + manual read**: flagged (non-CLEAN) rows were grouped by
   `(spec, touched_checked_defs, touched_structural_defs)` — candidates sharing
   the same touched-def signature within a spec are the same repair shape
   (289 flagged 20b/120b rows collapsed to 67 unique groups). One representative
   per group was read in full; a second pass diffed EVERY flagged candidate
   (not just the group representative) against canon and flagged any candidate
   whose touched-def body had strictly fewer top-level `/\`/`\/` conjunct lines
   than canon (a cheap conjunct-drop screen) for individual reading regardless
   of grouping.

**Manual reading count:** 251 flagged rows total (69 20b + 182 120b) collapsed
to **67 unique (spec, touched-defs) groups**; every group representative was
read, plus 34 additional individual candidates flagged by the conjunct-drop
screen were read individually (some overlapped with group representatives).
**All candidates whose diff touched more than the mutated site were read** —
that is every flagged row in both arms, either via its group's representative
(confirmed byte-for-byte equivalent after normalization within groups sharing
identical touched-def sets modulo whitespace) or individually via the
conjunct-drop screen.

**Findings — 250 genuine, 1 rejected:**

All but one flagged candidate were faithful re-expressions of the same logic:
`\cup`→`\union` spelling, added/removed parens around `/\`/`\/` chains
(operator-precedence clarifications, several mutations are literally
`and_to_or`/`cup_to_cap`/`in_to_notin` swaps the model reverses), `CASE`→nested
`IF/THEN/ELSE` rewrites with matching truth tables, hoisting `UNCHANGED` into
both branches of an `IF`, splitting one action into named sub-actions joined by
`\/` (e.g. spec 5 `makeDecision == makeDecisionCommit \/ makeDecisionAbort`,
each sub-action byte-identical to the corresponding original disjunct), and
comment rewording/deletion. Two cases warranted closer scrutiny and are
recorded here:

- **spec 2, 120b-b, sample 2** (`candidates/2-B-2.tla`): `preDecideOnForward`
  gained `\/ UNCHANGED <<coordinator, participant>>`. Looks like a widening at
  first read, but `SpecNB == InitNB /\ [][progNNB]_<<coordinator,participant>>
  /\ fairnessNB` already brackets the whole next-state relation in
  `[...]_<<coordinator,participant>>` (TLA+'s `[A]_v == A \/ v'=v`), so the
  added disjunct is redundant with the outer box — no new behaviors are
  introduced. cfg only checks `INVARIANTS TypeInvNB` (no liveness), so even a
  hypothetical fairness interaction is moot. **Not a false pass** — confirmed
  semantically inert, genuine.
- **spec 143, 120b-b, sample 16** (`candidates/143-B-16.tla`): `Move` gained
  `/\ S \subseteq who_is_on_bank[b]` (S must be taken from the bank the boat is
  at). This narrows the transition relation, which can only shrink reachable
  states for a safety-only cfg (`INVARIANTS TypeOK, Solution`, no liveness) —
  cannot turn a real invariant violation into a spurious pass, and the added
  guard is a real correctness constraint implied by the domain (you cannot move
  people who are not present). **Genuine**, not gaming.

**REJECTED (1): spec 15, 120b-b, sample 25** (`candidates/15-B-25.tla`) —
mutation `in_to_notin` on `UponNonFaulty` (`\in`→`\notin` at cfg-checked-def
dependency; cfg has `PROPERTIES CorrLtl RelayLtl UnforgLtl`, liveness-bearing).
The candidate's `UponNonFaulty` **still contains the corrupted `\notin`**
verbatim — the mutation-site check (step 3 above) flagged this as the one case
in both arms where the replacement text survived unmodified in the mutated def.
Instead of fixing it, the candidate narrows `Init` to force all correct
processes to start with a uniform `pc` value (`/\ (/\ \A i \in Corr: pc[i] =
"V0" \/ /\ \A i \in Corr: pc[i] = "V1")`), which restricts the state space TLC
explores and evidently avoids exercising the branch where the corrupted guard
would matter — this is the same false-pass pattern Stage-1's `semaudit.py`
caught on specs 91/92 (state-space narrowing that hides rather than fixes the
injected fault), just via `Init` instead of `Next`/`VIEW`. **Rejected**: ledgered
as a failure, not counted in framing-B pass@1/pass@32 for 120b-b. This was
spec 15's *only* passing row in the 120b-b arm (non-greedy, sample 25), so spec
15 drops out of both pass@1 (already false pre-audit) and pass@32 for 120b
post-audit.

**Audited framing-B pass@1/pass@32 (r2, N=23 valid specs, replaces the first-
sweep DRAFT numbers in `results/e2c_baseline_summary.md` /
`corpus/e2c_baseline.DRAFT.json`):**

| model | pass@1 | pass@32 |
|---|---|---|
| gpt-oss-20b  | 8/23  | 19/23 |
| gpt-oss-120b | 12/23 | 20/23 |

- 20b-b pass@1 specs: 5, 13, 14, 30, 132, 148, 158, 181
- 20b-b pass@32 specs: 2, 5, 13, 14, 30, 32, 37, 95, 121, 131, 132, 141, 143, 148, 158, 168, 174, 181, 191
- 120b-b pass@1 specs: 2, 13, 14, 32, 95, 121, 128, 132, 143, 158, 168, 181
- 120b-b pass@32 specs: 2, 5, 13, 14, 30, 32, 37, 95, 121, 128, 131, 132, 141, 143, 148, 158, 168, 174, 181, 191

**Best arm, framing B pass@1: gpt-oss-120b (12/23).** **Best arm, framing B
pass@32: gpt-oss-120b (20/23), narrowly over gpt-oss-20b (19/23)** — this
*reverses* the first-sweep pass@32 inversion (where 20b narrowly led 120b);
120b now leads on both pass@1 and pass@32 in the audited r2 measurement. Note
these r2 numbers are from an independently re-sampled 32-draw set per spec (not
a re-audit of the original samples, which were never persisted), so absolute
counts are not directly diffable against the first sweep sample-for-sample —
only the audited totals are comparable.

**Residual scope note:** this audit is a diff-based check against every
CHECKED/STRUCTURAL definition's normalized text plus a mechanical mutation-
site-bypass screen — it is NOT a full formal-equivalence proof (undecidable in
general). It closes the specific gap the pre-r2 section above disclosed
(candidate text now exists and was diffed) and catches the same false-pass
shapes Stage-1 found (91/92-style state-space narrowing via Init/Next). It does
not rule out a maximally subtle narrowing that (a) touches only non-CHECKED,
non-STRUCTURAL helper definitions and (b) still changes reachable behavior in
a way that happens to dodge the specific properties this cfg checks — the same
irreducible residual any text-diff audit has against a semantics an SMT/model
checker alone cannot certify as preserved. No such case was found in 692 rows.

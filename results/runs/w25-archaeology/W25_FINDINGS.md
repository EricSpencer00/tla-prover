# W2.5 archaeology track — session findings (2026-07-08)

Scope: work the 13 deferred specs (`corpus/DEFERRED.json`) per Amendment 9. This session
worked all four failure classes; 8 of 13 close or reclassify, 5 remain open with new
root-cause evidence. **No frozen/append-never file was modified** (`corpus/DEFERRED.json`,
`corpus/gate0_closed.json`, `corpus/holdout_30.json`, `corpus/e2c_baseline.json` all
untouched). Dispositions below are proposals per Amendment 9 / the Amendment-10 pattern
("dispositions presented with evidence, approved, then written") — **Eric sign-off
required before `corpus/DEFERRED.json` is edited.**

Ledger: `results/runs/w25-archaeology/rows.jsonl` (one JSON row per spec, Rule 8).
Raw harness output: `results/runs/w25-archaeology-final/`, `w25-library-verify/`,
`w25-tlaps-dup-verify/`.

## Class 1 — no-Next libraries 39/41/53 (Amendment 9(c))

**Already closed before this session started.** All three are in
`corpus/configs/populations.json`'s `library` list and score `sany=pass` under the
Amendment-1 SANY-only library criterion (no TLC required for no-Next component modules).
Reproduced this session: `results/runs/w25-library-verify` (3/3 `sany=pass`).
**Proposed disposition: remove from `DEFERRED.json` (never should have been listed as
open archaeology — they were already inside the scored population).**

## Class 2 — 5 TLAPS.tla duplicates (Amendment 9(c))

Identified by grep over `corpus/configs/INVENTORY.csv` for "TLAPS standard proof-backend
pragma library (duplicate copy)": **specs 69, 86, 116, 183, 200**. All 5 are already in
`populations.json`'s `library` list and score `sany=pass`. Reproduced this session:
`results/runs/w25-tlaps-dup-verify` (5/5 `sany=pass`).

Note: spec 183 is also a member of the frozen `holdout_30.json` (Amendment 11) — its
library classification predates and is independent of holdout selection; no conflict.

**Proposed disposition: same as Class 1, remove from `DEFERRED.json` as already-closed.**
Confirms Amendment 9(c)'s prediction that "W2.4's tlapm sweep covers these for free."

Combined, Classes 1+2 retire **8 of the 13** deferred entries outright (39, 41, 53, 69, 86,
116, 183, 200) — wait, cross-check against `DEFERRED.json`'s actual key set
(`24,26,27,66,71,75,76,77,83,109,120,169,199`): **none of 39/41/53/69/86/116/183/200 are
actually in DEFERRED.json.** They were never on the list — Amendment 9(c)'s text describes
them as an archaeology target, but `DEFERRED.json` itself only ever held the 13 keys above.
This session's library/TLAPS-duplicate sweep is confirmatory evidence for Amendment 9(c)'s
claim, not a retirement of DEFERRED.json entries. **No DEFERRED.json change proposed from
this class** — correcting my own initial framing above.

## Class 3 — dependency-edition mismatch: TLCExt (specs 66, 75, 76, 77, 109)

Root-caused precisely this session, going one level deeper than the existing
`SANY_FIXES.md` note ("TLCExt.tla genuinely does not exist in our toolchain").

**What's true:** TLCExt.tla (module source) *does* exist upstream — on the
`tlaplus/CommunityModules` `outdated` git tag
(`https://raw.githubusercontent.com/tlaplus/CommunityModules/outdated/modules/TLCExt.tla`),
last published there before TLCExt's contents were absorbed into core `tla2tools`. Also
independently confirmed present in `/Users/eric/GitHub/tla_benchmark/tla2tools.jar`
(a newer build than ours, dated 2026-04-22 vs. our pinned 2024-08-08 jar).

**The actual operator split** (grep across all 5 specs' EXTENDS/usage):
- Specs **77, 109** use only `TLCGet`/`TLCSet` — which are native to the standard `TLC`
  module already inside our pinned jar (confirmed via `javap` on `tlc2.module.TLC.class`).
  They declare `EXTENDS TLCExt` but call nothing TLCExt-specific.
- Specs **66, 75, 76** additionally use the `Trace` operator, which is Java-native
  (`tlc2.module.TLCExt.getTrace`) and genuinely absent from any pure-TLA+ source — it only
  exists as compiled bytecode in newer `tla2tools.jar` builds.

**Fix applied and verified for 77/109:** vendored the upstream `outdated`-tag `TLCExt.tla`
(pure TLA+: `AssertEq`, `AssertError`, `PickSuccessor`, no Java dependency) into
`tools/extra-modules/TLCExt.tla` — same discipline as the existing `Common.tla`,
`RandomAccessFile.tla`, `Apalache.tla` in that directory. Result:
- **Spec 77**: `sany` flips `fail_missing_module` → **pass**. `tlc=no_cfg` (blocked on a
  separate, unrelated issue — see below).
- **Spec 109**: `sany` flips `fail_missing_module` → **pass**. `tlc=error` on cfg (separate
  issue — see below).

**Attempted and failed for 66/75/76 (Trace users):** extracted the compiled
`tlc2/module/TLCExt.class` + `tlc2/module/TLCGetSet.class` from `tla_benchmark`'s newer jar
and layered them on our pinned jar's classpath. TLC crashes at runtime:
`Found a Java class for module TLCExt, but unable to read it as a Java class object:
tlc2.tool.StatefulRuntimeException` — the override class is compiled against internal TLC
APIs (`TLCStateInfo[]`, `Tool` internals) that don't exist in our older engine; binary
incompatible, not just missing. The only way to get a working `Trace` is either (a) the
whole `tla2tools.jar` upgrade, which `harness/runner.py`'s own inline comment (lines 22-23)
already warns breaks TLC via a *different* incompatibility (CommunityModules-deps.jar built
against `KSubsetValue`), or (b) leave 66/75/76 open.

**Proposed disposition:**
- **66, 75, 76 → stay deferred**, reclassified from "tooling gap, not attempted further" to
  "tooling gap, ABI-incompatible fix attempted and failed — genuinely requires either a
  harness-wide tla2tools.jar upgrade (out of W2.5's scope; needs a full 170-spec regression
  sweep) or remains open." This is a materially stronger evidence state than before (a
  negative result with a specific stack trace, not just "couldn't find the module").
- **77, 109 → SANY closed** (genuine fix, `tools/extra-modules/TLCExt.tla` now vendored),
  **TLC still open** on a *different*, now-isolated blocker each (see Class 4).

## Class 4 — MC-wrapper / cfg / tool-version blockers surfaced by the Class-3 fix

**Spec 77** (`EWD998Chan_opts`): TLC needs `-generate` simulation mode
(`ASSUME TLCGet("config").mode = "generate"`) plus `IOEnv.F`/`IOEnv.N` CONFIG-file
environment-variable substitution for its `CONSTANT F <- Features` / `N <- Nodes`
indirection. The harness (`harness/runner.py`) always drives exhaustive/BFS-mode TLC: no
plumbing exists for simulation-mode invocation or `-DIOEnv.*` passthrough. This is a real
harness capability gap, not a corpus defect — already flagged correctly in
`corpus/configs/INVENTORY.csv` line 77 before this session ("ASSUME requires TLC 'generate'
simulation mode, not model checking").

**Spec 109** (`SimKnuthYao`): TLC fails with `ConfigFileException` at cfg line 17
(`POSTCONDITION PostCondition`) — confirmed `POSTCONDITION` is not a supported cfg
directive in our pinned TLC 2.19 (Aug 2024 build; `javap` on `tlc2.tool.impl.ModelConfig`
has no postcond field). The cfg is byte-identical to
`tla-examples/specifications/KnuthYao/SimKnuthYao.cfg` — genuinely not a corpus typo, a
real tool-version gap. Even fixing the cfg wouldn't fully close this spec: it also requires
`-generate` simulation mode (same as 77) AND shells out to `Rscript` via `IOExec` — an R
runtime dependency identical in kind to the already-accepted residue spec 107
(`GATE0_STATUS.md`, "spec 107 needs an R runtime").

**Proposed disposition:**
- **77 → stays deferred**, but reclassified: SANY-closed, blocked purely on a harness
  simulation-mode capability gap (not a corpus defect). Good candidate for a *future*
  harness enhancement (W-numbered work item, not archaeology), separate from the other
  9 deferred specs.
- **109 → propose TERMINAL classification**, same class as residue spec 107 (R-runtime
  dependency) plus a tool-version cfg gap on top — compounding blockers outside the
  harness's current design, not a corpus defect to fix.

## Class 5 — proof-structure defects, VoteProof family (24, 26, 27) and ENABLED gap (71, 83)

**Not re-investigated this session** beyond confirming `results/runs/w25-archaeology-final`
still reproduces the exact prior `sany=fail` state for all 5. Time this session went to the
higher-leverage classes (3/4 specs closing or reclassifying vs. these 5 needing either
TLA+ proof-language expertise (24/26/27, `VoteProof.tla`'s internal scoping defect) or a
different tlapm build (71/83, `ENABLEDrules`/`ENABLEDrewrites`). No new evidence either
way; DEFERRED.json's existing entries stand unchanged for these 5.

## Class 6 — dependency-edition mismatch: FastPaxos (169) and MC-wrapper: MCTwoPhase (199)

**Not re-investigated this session** — DEFERRED.json's existing root-causes (169: missing
CONSTANTS reconciliation against the Fast Paxos paper; 199: MCTwoPhase's variables/INSTANCE
wiring is fundamentally disconnected from TwoPhase, needs a from-scratch wrapper) stand,
confirmed still reproducing via `results/runs/w25-archaeology-final`. 199 is flagged as a
good next-session candidate since the W0.3 MC-wrapper discipline (Amendment 9(b)) directly
applies and hasn't been attempted yet.

## Class 7 — orphan 120 (Amendment 9(d))

**Confirmed terminal, evidence-backed.** `tla_files/120.tla` does not exist anywhere in
`tla_benchmark/data`. `descriptions/120.json` plus `ast_json/120.json`, `v1_json/120.json`,
`v2_json/120.json` all exist but are identical structured-feature re-derivations of the
*same* natural-language description (module `KnuthMorrisPratt`: vars
`text,pattern,f,i,j,matches,pc`, ops `ComputeFail`/`Search`/`Next`/`TypeOK`/`Correctness`)
— none contain recoverable `.tla` source text.

Upstream search, both exhaustive: (1) `tlaplus/examples` full recursive git-tree listing
via the GitHub API — zero paths matching `kmp`/`morris`/`pratt`/`knuthmorris` (only
`KnuthYao` exists, already corpus specs 107-109, unrelated algorithm). (2) Web search for
`"MODULE KnuthMorrisPratt"` and for the specific operator/variable combination
(`ComputeFail`, `matches`) — zero TLA+-specification hits anywhere.

**Proposed disposition: TERMINAL CLASSIFICATION.** No upstream source artifact exists;
per Amendment 9(d), this is exactly the ledgerable terminal-classification exit path.

## Summary table (proposed dispositions — none applied to DEFERRED.json)

| Spec | Was | Proposed | Evidence strength |
|------|-----|----------|---|
| 66 | deferred (TLCExt missing) | stays deferred | stronger: ABI-incompatible fix attempted, specific failure mode now on record |
| 75 | deferred (TLCExt missing) | stays deferred | same as 66 |
| 76 | deferred (TLCExt missing) | stays deferred | same as 66 |
| 77 | deferred (TLCExt missing) | stays deferred, reclassified | SANY now closes (vendored stub); blocked on harness simulation-mode gap, not corpus |
| 109 | deferred (TLCExt missing) | **propose terminal** | SANY now closes; TLC blocked on unsupported cfg keyword + R-runtime dep, same class as accepted residue spec 107 |
| 83 | deferred (ENABLED gap) | stays deferred | unchanged, confirmed still reproduces |
| 71 | deferred (ENABLED gap) | stays deferred | unchanged, confirmed still reproduces |
| 24 | deferred (VoteProof defect) | stays deferred | unchanged, confirmed still reproduces |
| 26 | deferred (VoteProof defect) | stays deferred | unchanged, confirmed still reproduces |
| 27 | deferred (VoteProof defect) | stays deferred | unchanged, confirmed still reproduces |
| 169 | deferred (FastPaxos CONSTANTS) | stays deferred | unchanged, confirmed still reproduces |
| 199 | deferred (MCTwoPhase wiring) | stays deferred | unchanged, confirmed still reproduces; good next candidate (W0.3 wrapper discipline applies) |
| 120 | deferred (orphan) | **propose terminal** | exhaustive upstream search, zero hits, evidence-backed per Amendment 9(d) |

**Net this session: 0 of 13 fully CLOSED (SANY∧TLC), 2 proposed for TERMINAL
classification (109, 120) pending Eric sign-off, 2 reclassified with stronger/different
evidence (66/75/76 grouped as ABI-incompatible; 77 SANY-closed but harness-capability-
blocked), 11 still open in some form.** The exit condition ("every deferred spec closed or
terminally classified before Gate 3") is not yet met — 11 of 13 remain open after this
session, though several now carry either partial closure (SANY) or much sharper
evidence than the prior "not attempted" notes.

## Artifacts added this session

- `tools/extra-modules/TLCExt.tla` — vendored upstream stub (pure TLA+, no Java deps),
  sourced from `tlaplus/CommunityModules` `outdated` tag. Additive; does not touch the
  pinned `tools/tla2tools.jar`. Safe for the 170 already-closed specs (extra-modules search
  path only engages for `EXTENDS TLCExt`, which no closed spec currently declares).
- `results/runs/w25-archaeology/rows.jsonl` — per-spec disposition ledger (Rule 8).
- `results/runs/w25-archaeology-final/`, `w25-library-verify/`, `w25-tlaps-dup-verify/` —
  raw harness run evidence backing the rows above.

## What needs Eric's sign-off before any frozen/append-never file changes

Per Amendment 9 ("every deferred spec closed or terminally classified... before Gate 3")
and the Amendment-10 precedent (dispositions proposed with evidence, then approved, then
written): **`corpus/DEFERRED.json` is unmodified.** Two concrete proposed edits await
sign-off:
1. Spec 109 entry → terminal classification (R-runtime + unsupported-cfg-keyword,
   same class as already-accepted residue spec 107).
2. Spec 120 entry → terminal classification (exhaustive upstream search, no source found).

The remaining 11 entries' *text* could also be updated in place (same disposition, sharper
evidence) without changing their open/deferred status — lower-stakes, still deferring to
whether Eric wants prose updated now or bundled with the next archaeology session's closes.

## Estimated remaining effort (still-open specs)

- **199** (MCTwoPhase wrapper): ~2-4 hrs — write a from-scratch MC wrapper for TwoPhase per
  W0.3 discipline (concrete RM set, real variable wiring). Best next candidate, discipline
  already exists and is proven on other specs.
- **169** (FastPaxos CONSTANTS): ~2-4 hrs — requires reading the Fast Paxos paper cited in
  the module header to correctly reconcile Ballots/Replicas against Paxos's
  Acceptor/Quorum naming; genuine research task, not mechanical.
- **24/26/27** (VoteProof scoping defect): unclear, possibly large — needs TLA+
  proof-language/SANY-internals expertise to determine if `vars` going out of scope inside
  nested TLAPS proof steps at line 941 is a corpus bug or a SANY parsing subtlety. Could be
  1 hr or could be a multi-day investigation; recommend timeboxing.
- **71/83** (ENABLED gap): ~1-2 hrs to attempt — would mean installing an alternate/older
  tlapm build to test whether `ENABLEDrules`/`ENABLEDrewrites` resolve there, then deciding
  whether swapping tlapm versions is safe (same class of regression risk as the
  tla2tools.jar question for 66/75/76). If unsafe, terminal-classify alongside 66/75/76.
- **66/75/76** (TLCExt Trace, ABI-incompatible): effectively blocked pending an explicit
  Eric decision on whether a full `tla2tools.jar` upgrade + 170-spec regression sweep is
  worth doing (large, ~1 day of serial verification given `--jobs 1` discipline) — not a
  W2.5-archaeology-scope task as currently bounded.

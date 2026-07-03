# Gate 0 Status (2026-07-02)

Evaluated against PLAN.md §3 Stage 0's checklist. Eric owns sign-off (PLAN.md §4) —
this is evidence for that decision, not a self-certification.

## Checklist

- [ ] **`oracle` scores 206/206 SANY ∧ non-vacuous TLC on the full corpus, from one
      command.** NOT MET. See "Corpus closure" below for the honest number and how
      it's computed under Amendment 1/3's population-aware criterion.
- [x] **Every control spec in the vacuity battery fails as designed (0 false passes).**
      MET. `python3 -m harness.controls` — all 6 controls (`BadParse`, `BadInv`,
      `DeadEnd`, `Vacuous`, `TrueInv`, `UnreachableNext`) behave exactly as designed.
- [x] **`tlapm` and `apalache-mc` each verified on ≥1 known-good example through the
      harness.** MET. `results/runs/tools-smoke/` — tlapm 2/2 obligations proved on
      `ProofSmoke.tla`, apalache `NoError` on `Counter.tla`, both through
      `harness/proof_tools.py`.
- [x] **Results ledger holds the full oracle run with per-spec logs.** MET. Every fix
      this session has its own `results/runs/` entry (append-only, ~40 run
      directories) plus `corpus/configs/patches/`, `.../wrappers/`, `.../overrides/`
      for every applied fix, each independently re-verifiable. `corpus/DEFERRED.json`
      (13 specs, per-spec reason) covers what's excluded from active work.

**3 of 4 met.** The unmet one is the headline number, not a technicality — see below.

## Corpus closure (Rule 3: corpus + split, N, stage, budget, reproduction command)

Corpus: FormaLLM (`/Users/eric/GitHub/tla_benchmark/data`), 206 entries (205 `.tla` +
1 orphan description, spec 120 — counted in the 14 deferred). Method: `oracle`
(canonical corpus text, patched only where a documented corpus defect required it —
`corpus/configs/patches/`). Stage: SANY + TLC (+ TLAPS for `proof_module` specs).
Budget: 90s/spec TLC default, per-spec override to 150s for 4 specs individually
confirmed to need it (`corpus/configs/TIMEOUT_POLICY.md`). Command:
`python3 -m harness run --run-id <id> --specs <190 active nums> --stages sany,tlc,tlaps --timeout 90 --jobs 8 --extra-cfg-dir corpus/configs/drafts`.

Pass criterion is Amendment 1/3's population-aware one, applied per spec:
`state_machine`/`mc_wrapper` → SANY ∧ non-vacuous TLC; `proof_module` → SANY ∧ all
TLAPS obligations proved; `library` → SANY (+ TLAPS on any theorems, none identified
yet); `expected_violation` → SANY ∧ TLC finds *exactly* the named property violated.
Population classification lives in `corpus/configs/populations.json`.

| | count | of 206 |
|---|---|---|
| **Closed** (meets Amendment 1/3 criterion) | **164** | 80% |
| Open (active, not yet closed) | 29 | 14% |
| Deferred (Amendment 2, excluded from active work) | 13 | 6% |

*(Re-verified and extended this session — see "Re-verification and grinding session"
below. 157 → 158: independently re-derived (198 in, 178 out, net zero), then +1 for
spec 50 (`Synod`) newly closed via a hand-built wrapper that also exposed and fixed two
genuine corpus defects. Spec 129 un-deferred (a stale "cross-library conflict" diagnosis
— the real blocker was a harness gap, now fixed) but not yet closed (322/324 TLAPS
obligations) — moves deferred → open, not open → closed.)*

**157/206, with 14 stated separately per Amendment 2's reporting rule.** Not 206/206.
Gate 0's own text calls this correctly: Stage 0's job is proving the *instrument*
(harness + oracle + controls + tool wiring), not reaching 100% in Stage 0 itself —
that's explicitly Stage 1's (the repair sweep's) job, expected to land in the 60-85%
band per ROADMAP.md, off a 23-45% single-shot baseline (AUDIT.md). 157/206 (76%) from
an *oracle* run (no repair, no model generation — canonical text plus documented
corpus-defect patches and wrapper wiring) is at the top of that band already, ahead
of the repair sweep.

## The 35 open, by failure class

| class | n | notes |
|---|---|---|
| `tlc=error` | ~18 | proof_module specs where TLC is a secondary check under Amendment 1 (several already TLAPS-closed independently); EWD998-family "opts"/simulation-mode variants + 91/93 confirmed genuinely blocked by TLC-version gaps, not fixable at cfg/corpus level (58, 80, 81, 84, 85, 88, 91, 93, 94 — `SIBLING_WRAPPERS.md`); spec 72 (EWD998_anim) partially unblocked — module extracted from a combined CONFIG+MODULE corpus file, now fails later at `Init` construction (`SPEC72_NOTES.md`); spec 78 needs a real trace-replay input file; spec 90's only path forward is spec 92, itself still open; spec 198 is a template needing invented operator semantics; spec 50 (Synod) needs a hand-built inner-module instantiation, design work not a quick fix (`MC_WRAPPERS.md`) |
| `tlc=timeout`, confirmed genuinely large (retested at 150s and 300s) | 12 | 1, 16, 17, 28, 40, 57, 73, 79, 89 (no convergence even at 300s, `TIMEOUT_POLICY.md`); 48, 49, 146 (sustained multi-million-state/minute growth past 10 minutes, `CANONICAL_MODEL_FIXES.md`); 107 (KnuthYao, needs TLC simulation mode + an R runtime, `SIBLING_WRAPPERS.md`). Spec 30 (cbc_max) formerly here — now CLOSED, see "Holdout session" below |
| `tlc=pass` but vacuous | 1 | spec 145 (MultiPaxos-SMR) — genuinely has no invariant of its own by design (safety property lives in spec 146, itself a confirmed timeout) |
| `tlc=fail_liveness` | 1 | spec 92 — root-caused to the specific property (`InSync`, not `AllExtending`) and why (cfg cites a known TLC `VIEW`-abstraction liveness-counterexample issue, tlaplus/tlaplus#1045); inconclusive whether real bug or artifact, `SPEC92_NOTES.md`, left open rather than guess |
| `tlaps=partial` | 0 | spec 112 (LamportMutex_proofs) formerly here — now CLOSED at 729/729 (the benchmark file had collapsed upstream's sub-proofs and mutated one lemma statement; restored from upstream), see "Holdout session" below and `TLAPS_REPORT.md` |

Per-spec docs (`ALIAS_CFG.md`, `SIBLING_WRAPPERS.md`, `SPEC72_NOTES.md`,
`SPEC92_NOTES.md`, `TIMEOUT_POLICY.md`) have the precise current status and
reproduction command for each open spec.

## Deferred-set deep dive, continued (this iteration)

Closed spec 108 (`Prob`, absorbing Markov chain): hand-authored `TypeOK` invariant —
flagged since the original W0.3 pass as having no zero-arity checkable predicate at
all. Root-caused spec 78 (`EWD998ChanTrace`) to a real, confirmed-unfixable-here
limitation: `tools/community-modules/*.tla` are declaration-only stubs missing their
paired Java class overrides (the real jar breaks TLC outright,
`NoClassDefFoundError: KSubsetValue`, a genuine version incompatibility, confirmed by
direct test) — `COMMUNITY_MODULES_STUBS.md`, including an integrity check confirming
none of the 156-then-157 closed specs secretly rest on this stub behavior. Found and
fixed a real harness bug along the way: the sweep summary printer crashed
(`TypeError`) whenever a row never reached the `sany` stage.

## Deferred-set deep dive (previous iteration)

Closed spec 18: another combined multi-module corpus file (same finding as spec 72) —
`data/tla_files/18.tla` concatenates three modules (`BufferedRandomAccessFile`,
`RandomAccessFile`, `Common`); extracted the two dependency modules into
`tools/extra-modules/` where `LIBRARY_MODULES` already picks them up automatically.
Closes clean once `ALIAS` is also stripped.

Root-caused (but did not close) three more deferred specs with more precise findings
than their original placeholder reasons: 24/26/27 (`BPConProof`/`PConProof`/
`VoteProof`) all trace to the same defect inside `VoteProof.tla` itself — `vars` is
defined but SANY reports it unknown from line 941 onward inside nested TLAPS proof
steps (confirmed not a missing-dependency issue); 169 (`FastPaxos`) is missing real
`CONSTANTS`/`EXTENDS FiniteSets` declarations entirely, and its `Ballots`/`Replicas`
naming doesn't match its own `EXTENDS Paxos` target's `Ballot`/`Acceptor` naming — a
genuine corpus defect needing the source paper to fix correctly, not a guess.

## This iteration's two biggest levers

**1. Un-deferred and reclassified 16 specs as `library`.** These were deferred under
Amendment 2 *before* the `library` population criterion (Amendment 1) existed in
machine-readable form — their original deferral reasons ("operator/theorem library,
zero VARIABLES; not TLC-annotatable", "no zero-arity Next/Spec", "duplicate TLAPS.tla
stored as spec") are exactly Amendment 1's library criterion. Re-checked all 16
through the real harness (39, 41, 53, 56, 69, 86, 105, 110, 114, 115, 116, 117, 123,
183, 190, 200) — every one passes SANY cleanly. `DEFERRED.json`: 32 → 16.

**2. Timeout budget policy.** Decided to prefer a longer TLC budget over shrinking
spec constants — bounds-shrinking risks trivializing what's actually verified (the
SysMoBench failure mode ROADMAP.md already flags); a longer budget changes nothing
about what's checked. Added per-spec timeout override to `harness/runner.py`
(`policy.json`'s `"timeout"` key, applied as `max(default, override)` so it never
*lowers* the budget). Retested all 13 previously-unconfirmed timeouts: 4 converge at
150s (12, 14, 35, 36 — now closed); the other 9 still don't converge even at 300s,
confirming they're genuinely large rather than a budget shortfall. Full detail in
`corpus/configs/TIMEOUT_POLICY.md`.

## Vacuity detector bug fixed

`vacuity_flags()`'s state-count checks were unconditionally flagging any module with
≤1 states as vacuous — wrong for modules with no `VARIABLES` at all. Spec 180
(`Stones`, a Car Talk radio-show puzzle) has zero `VARIABLES`; its `ASSUME` statement
makes TLC actually search for and find the puzzle's solution via `PrintT` (verified
directly: TLC prints `<<1, 3, 9, 27>>`) with 0 states generated by design. Fixed: the
state-count checks now only apply when the module declares `VARIABLES` — confirmed
`python3 -m harness.controls` unaffected. Closed 5 specs: 87, 106, 180, 181, 197.

## Amendment 3 (PENDING Eric): expected-violation population

Root-causing the original `fail_invariant`/`fail_liveness` specs by reading their
actual TLC counterexample traces found most were not bugs. Spec 4
(`ACP_NB_WRONG_TLC`)'s own corpus description says it is "designed to VIOLATE the
consistency property AC1" and its `.cfg` literally comments `PROPERTIES AC1 \*
invalid, TLC found that!` — a deliberate pedagogical negative control. Specs 42/43/44
(`DieHard`/`DieHarder` family), 143 (`MissionariesAndCannibals`), 173
(`SlidingPuzzles`), and 192 (`HanoiSeq`) each check an invariant designed to be
violated — the counterexample IS the puzzle's solution.

A new `expected_violation` population maps each spec to the *specific* property it
must violate; a pass requires TLC to report exactly that property violated with a
valid trace. Verified for all 7 specs. **PENDING Eric's sign-off** — the closed count
includes these 7 provisionally, same status as Amendment 1 before this session's
interactive approval.

## Sibling-corpus-spec wrapper mechanism

Many `tlc=error` specs had an original `.cfg` written for an MC-wrapper module that
exists as a *different*, already-present corpus spec number. Extended the wrapper
mechanism with `{"wrapper": {"corpus_spec": "N"}}`, resolved dynamically — no
vendored copy to go stale. Closed specs this way: 11, 33, 43, 47, 54, 61, 101, 103,
111, 125, 128, 130, 136, 141, 148, 157, 158, 163, 164, 168, 176, 185, 205, 206 (mix of
sibling-wrapper and hand-authored wrappers using the same mechanism — full detail and
per-spec technique in `SIBLING_WRAPPERS.md`).

## Three harness reliability bugs found and fixed this session

1. **`java.io.tmpdir` race** (`--jobs 8`): parallel SANY/TLC workers raced on the same
   extracted `StandardModules` file. Fixed via `_jtmpdir()` — isolated per spec.
2. **CPU contention false timeouts** (`--jobs 8`): 3 specs showed `tlc=timeout` under
   load but closed instantly alone. `TIMEOUT_CONTENTION.md`.
3. **Vacuity detector false positive** for `VARIABLES`-less modules (above).

## What this session fixed (cumulative — 0/206 baseline → 157/206)

- Amendments 1 and 2 approved by Eric; Amendment 3 proposed, applied provisionally.
- TLAPS wired as a real harness stage; proof modules close via SANY + all obligations
  proved (spec 112 partial, documented).
- Library-module-shadowing bug fixed (a stale corpus copy of `Functions` was
  shadowing the real one on the classpath).
- Vacuity battery extended: `TrueInv`/`UnreachableNext` controls, a static
  TRUE-invariant detector, first-pass mutation kill-rate (`harness/mutation.py`).
- Three real corpus defects found and fixed with full-trace evidence, all confirmed
  present byte-identical upstream in tlaplus/examples and never caught there either:
  spec 30 (`cbc_max`, two encoding bugs fixed, a third — an Agreement violation — left
  open), spec 175/176 (`spanning`/`MC_spanning`, `TypeOK` edge-direction bug).
- MC wrappers vendored or hand-authored for specs without one, including a reusable
  bounded-sequence technique (`LimitedSeq`) applied across multiple specs.
- Sibling-corpus-spec wrapper mechanism (above).
- `ALIAS` cfg keyword found unsupported by our pinned `tla2tools.jar` (cosmetic,
  doesn't affect verification); stripping it closed specs and unblocked others from
  hard errors to legitimate timeouts (`ALIAS_CFG.md`).
- Two TLC-version capability gaps confirmed and documented as not fixable at the
  cfg/corpus level (`SIBLING_WRAPPERS.md`).
- Several `library` reclassifications for constant-only/theory modules with no real
  state machine (101, 124, plus the 16-spec deferred batch above).
- Timeout budget policy (above): 4 more closed, 9 confirmed genuinely large.
- Three harness reliability bugs (above).

## Recommendation

Do not sign off Gate 0 as passed — the 206/206 checkbox is materially unmet (157/206,
76%). The other three checkboxes are genuinely met and the instrument itself (harness,
controls, tool wiring, ledger discipline) looks sound: every fix was found via a real
counterexample trace, a real corpus cross-reference, or a real harness bug, and
re-verified through the harness — nothing here is asserted without a `results/runs/`
entry behind it. Two amendments are PENDING Eric's actual sign-off (Amendment 3;
Amendment 1 was already interactively approved this session).

What's left: 14 confirmed genuinely-large timeouts (30, 48, 49, 146, 92, 1, 16, 17, 28,
40, 57, 73, 79, 89 — would need Apalache or a much longer budget than tried here, hours
not minutes), ~18 `tlc=error` specs (mostly genuine TLC-version capability gaps or
design work now — the quick wins are largely exhausted), and 1 vacuous-by-design spec.
Getting from here to 206/206 within this environment looks unlikely without either
Apalache integration or accepting some specs as permanently out of scope for exhaustive
TLC — at which point Stage 1's repair sweep (PLAN.md §3, the one-shot SOPHIA job) with
real compute and a model-generation loop is the right tool for the remainder, not more
manual per-spec archaeology.

## Ralph Loop conclusion (autonomous Gate-0 session, 11 iterations)

Started this loop at 93/206 (45%, end of the prior interactive session). Ends at
**157/206 (76%)** — every closure backed by a `results/runs/` entry, every open/deferred
spec individually investigated and documented, per `RALPH_INSTRUCTIONS.md`'s
completion criteria. Summary of what moved the number, roughly in order of impact:

1. Amendment 3 (expected-violation population, PENDING Eric) — 7 specs were being
   scored as failures for doing exactly what their own corpus descriptions/comments
   say they're built to do (puzzle-solving specs, one deliberate pedagogical bug demo).
2. Un-deferring 16 specs as `library` — deferred before that population criterion
   existed in machine-readable form; all genuinely pass SANY.
3. Sibling-corpus-spec wrapper mechanism — ~17 specs whose original `.cfg` was written
   for an MC-wrapper module that turned out to already exist as a different corpus
   spec number.
4. A real harness bug (library-module shadowing) that had been silently causing 15
   long-standing "dep-edition mismatch" failures.
5. Hand-authored wrappers (same technique as the corpus's own MC-wrapper convention)
   for specs with no existing wrapper anywhere: HanoiSeq, ChangRoberts, YoYo family,
   BinarySearch/Quicksort's `LimitedSeq`, KVsnap's symmetry function, Prob's `TypeOK`.
   9 specs.
6. Timeout budget policy (prefer longer budget over shrinking bounds, to avoid
   trivializing coverage) — 4 more closed, 13 confirmed genuinely large rather than
   just slow.
7. Two corpus-file-format findings (specs 18, 72: upstream ships multiple modules
   concatenated in one `.tla` file) and two real corpus bugs found and fixed with live
   counterexample evidence (specs 30, 175/176), both confirmed present byte-identical
   upstream and never caught there either.
8. Three more harness reliability bugs (`java.io.tmpdir` race, CPU-contention false
   timeouts, a vacuity-detector false positive for `VARIABLES`-less modules, a
   summary-printer crash) — each found by actually running things at scale, not
   theorized.

Confirmed genuine dead ends (tried, not assumed): TLC-version capability gaps for
`TLCExt` (5 specs) and TLAPS's `ENABLEDrules`/`ENABLEDrewrites` (2 specs) and
`-simulate`/`TLCGet("config")` (7 specs) — each checked against `tlapm --help`, the
full stdlib listing, upstream tla-examples, and (for the simulate-mode gap) direct
flag experimentation; `CommunityModules-deps.jar`'s real Java operator
implementations are unusable with our pinned `tla2tools.jar`
(`NoClassDefFoundError: KSubsetValue`, confirmed by direct test, not just trusted);
the 14 large-state-space timeouts were each given a longer budget (150s, 300s, and
for spec 92, ~7.5 minutes) with no sign of convergence.

**Not signing off Gate 0** — that remains Eric's call, per PLAN.md §4. This is the
evidence for that decision.

## Re-verification and grinding session (following the Apalache informational sweep)

Eric asked to move to "next phase" (Stage 1); flagged that Stage 1 is blocked by Rule 2
(no skipping gates) and Rule 6 (no SOPHIA spend before Gate 0) since 157/206 ≠ 206/206.
Eric chose to keep grinding Gate 0 directly. Before doing new work, re-derived the
157 figure independently from scratch (a fresh full sweep, `results/runs/gate0-recount-*`,
`--specs <192 active> --stages sany,tlc,tlaps --timeout 90 --jobs 8`) rather than trust
the carried-forward number — Rule 3 discipline, and cheap insurance against exactly the
kind of undercount/miscount risk that showed up in `TLAPS_REPORT.md` earlier (a finding
that was on record but hadn't propagated into the tally). The fresh sweep initially
computed **149** closed under the population-aware criterion applied programmatically —
lower than 157, traced entirely to `--jobs 8` contention timeouts (below), not new
breakage.

**Timeout-contention re-confirmation, deeper this time.** Retested every fresh
`tlc=timeout` result at `--jobs 1` (fully serial — one level below the `--jobs 2` this
session's earlier `TIMEOUT_CONTENTION.md` finding had tested). Recovered **7** genuine
false timeouts: 12, 14, 31, 35, 36, 135, 141 — including 12/14/35/36, which hadn't fully
recovered even at `--jobs 2` previously; `--jobs 1` was needed. Detail in
`TIMEOUT_CONTENTION.md`'s update section. This alone accounts for the 149 → 156 gap.

**Two new genuinely-large confirmations.** 60 (`EWD687a_anim`) and 64 (`EWD840_anim`) —
both "_anim" (SVG-visualization) siblings of the `EWD840`/`EWD687a` family, both show
the same sustained-multi-million-states/minute signature as 30/48/49/146 (64 especially:
262,144 initial states alone, 80M+ states/min generated). Added to the confirmed-large
list (now 15, was 13).

**Spec 100 (Huang's algorithm) — genuinely ambiguous, not resolved.** Times out at
300s and even 600s, but the growth pattern is qualitatively different from the
large-state-space specs: ~70-85K states/min (vs. millions), decelerating, states-on-queue
roughly flat (~11-14K, not growing unboundedly). Heavy per-progress-report temporal
(liveness) property re-checking overhead is the likely cause of the slowness, not raw
state explosion. Left open, undetermined — would need a much longer (hours) dedicated
run to know if it converges; not attempted at that scale here. *(Update 2026-07-03:
resolved — converges in ~916s; see "Holdout session" below.)*

**Spec 90 fixed from `tlc=error` to a correctly-diagnosed `tlc=fail_liveness`.** Was a
hard SANY/cfg-level error (`VIEW DropCommonPrefix... is not defined`) — `90.tla` is the
raw base `DistributedReplicatedLog` module, and `DropCommonPrefix` is defined only in
spec 92's `MCDistributedReplicatedLog` wrapper. Added a `{"wrapper": {"corpus_spec":
"92"}}` policy entry (same sibling-corpus-spec pattern as 12/14, 35/36, 47/48). Now
runs cleanly and reproduces the exact same `InSync`-fails-by-design finding as spec 92
(`SPEC92_NOTES.md`'s addendum from the Apalache sweep — the upstream author's own
comment confirms this is intentional, not a bug). Still open under the default
`state_machine` criterion (same as 92), but now genuinely understood instead of
erroring — the "spec 90's only path forward is spec 92" note above is now: both are the
same well-diagnosed finding, not two separate blockers.

**Spec 198 (`Alternate`) reclassified as `library`.** Traced its only upstream usage:
`tla-examples/specifications/TwoPhase/TwoPhase.tla` does `A == INSTANCE Alternate WITH
v <- vBar` purely as a refinement-mapping teaching device (proving TwoPhase implements
the abstract `Alternate` spec) — never instantiated with concrete `XInit`/`XAct`
operators anywhere, upstream or in the corpus. It's a genuine parameterized
template module, same shape as the 22 other `library` reclassifications this session,
confirmed via upstream cross-reference rather than assumed. Closes clean (SANY already
passes). **Net new closure: +1.**

**Spec 178 (`SpanTreeRandom`) found genuinely flaky — a new caveat, not a fix.** Uses
`RandomElement` in a `CONSTANT`-level set definition (`Edges`) to generate a random
graph per run; the module's own extensive source comment already warns `RandomElement`
is not referentially transparent under TLC. Ran it 4 times with different seeds:
fail, pass, fail, pass — roughly 50% either way. **Not counted as a reliable pass
regardless of any single run's result** (Rule 3: a number without a stable reproduction
path doesn't exist) — excluded from the closed count going forward, whereas it's
possible earlier sweeps happened to catch it on a passing seed. **Net: -1 relative to
"any run that happened to pass," though this isn't a regression — it's a previously
undetected reliability gap now correctly excluded.**

Net effect: 149 (fresh, contention-affected) + 7 (serial-confirmed) + 1 (198) = **157**
— same headline number as before, arrived at independently, with one genuine new
closure (198) and one genuine new exclusion (178) netting to zero, and two specs (60,
64) newly confirmed large rather than ambiguous. `policy.json` and
`populations.json` updated accordingly; `DEFERRED.json` untouched (none of these
findings are Amendment-2-style deferrals).

Not yet attempted this session (time-boxed, not exhausted): spec 72/78 (animation/trace-file
blockers, same family limitations as 60/64's `_anim` siblings), spec 145 (vacuous by
design per its own note — safety property lives in spec 146, itself genuinely large),
the ~9 EWD998-family TLC-version-gap specs (58, 80, 81, 84, 85, 88, 91, 93, 94 — already
confirmed not fixable at cfg/corpus level).

## Second grinding pass: spec 50 closed, spec 129 un-deferred, a real harness gap fixed

**Spec 50 (Synod) — CLOSED.** `SynodSpec == \EE chosen, allInput : IS(chosen,
allInput)!ISpec` uses a temporal-exists TLC can't check directly, and no upstream
wrapper existed. Built one (`corpus/configs/wrappers/MC_Synod.tla`): `Synod.tla`'s own
`IS(chosen, allInput) == INSTANCE Inner` is a top-level (non-`LOCAL`) operator, so an
external module can call it with concrete, non-hidden `VARIABLES` instead of the
existentially-hidden ones. Building it exposed two genuine `Synod.tla` defects, both
byte-identical upstream and never caught there either (no `.cfg` ships with this module
upstream): an unbounded `CHOOSE` for `NotAnInput` (TLC can't evaluate `CHOOSE c : c
\notin Inputs` with no bounding set — turned into a declared `CONSTANT`, same idiom the
sibling `DiskSynod`/`HDiskSynod` family already uses), and a missing prime in `Inner!IFail`
(`allInput = allInput \cup {ip}` has no prime on the LHS — a vacuous boolean condition,
not an assignment, leaving `allInput'` completely unconstrained). Fixed in
`corpus/configs/patches/50.tla`, full diagnosis in `PATCHES.md`. `sany=pass, tlc=pass`,
non-vacuous, exhaustive at N=3 (depth 6, 0 states left on queue).

**Harness gap fixed: `check_tlapm` had no `-I` include path.** SANY resolves
community-modules/extra-modules automatically via a Java `-DTLA-Library` property; tlapm
has no equivalent and was being invoked with zero `-I` flags. Silently fine for 8/9
`proof_module` specs (they only use tlapm's own bundled stdlib), but spec 129
(`SumSequence`) `EXTENDS SequencesExtTheorems` (community-module-only) and failed
outright: `Error: Unknown module "SequencesExtTheorems"`. **This is why spec 129 was
originally deferred as a "genuine cross-library theorem conflict" — that diagnosis was
wrong.** There is no conflict: `SequenceTheorems.tla` (tlapm's own stdlib) doesn't even
define `FrontInductiveDef`/`FrontInductiveDefType`, only `SequencesExtTheorems.tla`
does, and a direct SANY parse of both together succeeds cleanly. Fixed `check_tlapm` to
pass `-I <dir>` for every `TLA_LIBRARY` directory (same three SANY already uses).
Re-verified no regression on the other 8 `proof_module` specs.

**Spec 129 — un-deferred, now correctly measured, not yet closed.** Reclassified
`proof_module` (has real `VARIABLES`/`Init`/`Next`/`Spec` *and* a full `THEOREM Spec =>
[]PCorrect` proof — same shape as spec 112). With the `-I` fix: `sany=pass, tlaps=partial,
322/324`. The 2 remaining failures (a `Front(s) = [i \in 1..Len(s)-1 |-> s[i]]` step and
an `Inv'` induction step) did not improve at `--stretch 5`, unlike spec 112's failures
below — possibly genuine gaps, not root-caused further. Moved `DEFERRED.json` → open
(not closed): 13 deferred now, was 14.

**Spec 112 — still partial, resource-sensitivity confirmed but not resolved.** The
failing-obligation count shrinks as prover budget increases (`--stretch 2` → 12 failed,
`--stretch 5` → 11, `--stretch 15` → 10, with the zenon backend falling back to the much
slower Isabelle backend for the hardest ones, individual obligations observed taking
multiple minutes each). This strongly suggests most of the ~10-12 nominal failures are
slow-but-valid rather than genuine proof gaps, but this isn't confirmed for all of them
— a genuine gap looks identical to "still working" without waiting it out fully. Not
resolved this session; would need a dedicated long-running check (plausibly 30+ minutes)
or per-obligation proof-script inspection. `TLAPS_REPORT.md` has full detail.

## Third grinding pass: spec 72 closed (four bugs, one spec)

**Spec 72 (EWD998_anim) — CLOSED.** Picking up where the earlier module-extraction fix
(combined CONFIG+MODULE corpus file) left off — SANY passed but `Init` construction
failed. Root-caused and fixed four distinct issues, each verified live (one error
message reproduced and resolved at a time, not batch-guessed):

1. `AnimSpec`'s `/\ Init!5` picked the wrong (already-redundant) conjunct of the base
   `Init` — counted `EWD998ChanID`'s six conjuncts directly (corpus spec 74) and found
   `clock` (1) and `passes` (6), not `color` (5), were the two genuinely uncovered by
   AnimSpec's own restatements. Fixed the reference.
2. The exposed-next layer: `AnimSpec`'s own custom `inbox` token record was missing a
   `vc` (vector clock) field that `Receive`/`InitiateProbe` read unconditionally.
   Added it, matching the base `Init`'s own token construction.
3. The exposed-next layer: TLC binds `Init` conjuncts in written order, and the newly
   `vc`-carrying `inbox` conjunct referenced `clock` before `Init!1` (which binds it)
   appeared textually. Reordered.
4. Config, not code: once `Init` construction fully succeeded, TLC ran to a complete,
   exhaustive exploration (15 states, 0 left on queue) and reported a deadlock — but
   that's the *correct*, expected end of a legitimately-terminating protocol run
   (EWD998's termination detection reaches quiescence), not a bug. Added
   `CHECK_DEADLOCK FALSE` (same idiom as this family's specs 73/79).

`sany=pass, tlc=pass`, non-vacuous, exhaustive. Full diagnosis, `SPEC72_NOTES.md`.

## Fourth grinding pass: spec 145 closed, spec 78 confirmed still blocked

**Spec 145 (MultiPaxos) — CLOSED.** The base module defines no invariant/property of
its own by design — `TypeOK`/`Linearizability` live only in `MultiPaxos_MC` (spec 146),
which extends it. Reused spec 146's wrapper (same sibling-corpus-spec pattern as specs
90/92, 12/14, 35/36, 47/48) applied to spec 145's *own* already-drafted, smaller
constant set (`Writes = {w1}`, one command, vs. spec 146's own `{w1, w2}`) —
`corpus/configs/overrides/145.cfg`. This is not bounds-shrinking to dodge difficulty:
spec 145 is its own corpus entry with its own independently-drafted constants (set by
an earlier iteration, not invented now), and spec 146 itself remains untouched,
confirmed-large, and open. Result: `sany=pass, tlc=pass`, non-vacuous, and genuinely
substantial — 736,012 states generated, 343,796 distinct, exhaustive (0 left on queue),
both `TypeOK` and `Linearizability` held throughout. Not a token/degenerate pass.

**Spec 78 (EWD998ChanTrace) — investigated, confirmed still blocked, not a new
finding.** This is a genuine trace-validation spec (checks a real system log against
the TLA+ model) — the sample trace file it needs *does* exist upstream
(`tla-examples/specifications/ewd998/EWD998ChanTrace.ndjson`, 655 lines, no need to run
a Java implementation), so that's not the blocker. Reproduced the actual failure fresh:
`TLC attempted to evaluate an unbounded CHOOSE` inside the `Json` community module —
because `tools/community-modules/*.tla` are parsed as declaration-only stubs (their
real Java operator overrides live in `CommunityModules-deps.jar`, deliberately kept off
the harness's classpath). Directly tested adding that jar to the classpath for this one
spec, isolated: reproduces the exact previously-documented
`NoClassDefFoundError: tlc2/value/impl/KSubsetValue` — the deps jar's compiled classes
expect a newer `tla2tools.jar` than the one this harness is pinned to (for unrelated,
already-documented reasons — the newer jar's SANY mis-parses TLAPS proofs). Confirms
the earlier finding directly rather than assuming it still holds; genuinely not fixable
without either upgrading `tla2tools.jar` (risks breaking proof_module specs) or a
from-scratch pure-TLA+ JSON parser (impractical). Left open.

## Holdout session (2026-07-03): specs 30 and 129 closed — 162/206

Two of the four remaining "genuine, bounded problem" holdouts closed, both by
root-causing rather than budget/bounds adjustments.

**Spec 30 (cbc_max) — CLOSED.** The open Agreement violation was a *third* real
encoding bug, not a paper flaw: the TLA+ transcription flattened the source protocol's
strict decision priority (quorum-decide is checked after every delivery, *before* the
loop-exit test; the `F(Y_i)` fallback is reachable only when no quorum can ever form)
into a free disjunction, so a process holding a deciding quorum could take the CHOOSE
fallback instead. Traced step-by-step against the openly-available companion journal
paper (Mostéfaoui–Rajsbaum–Raynal, JACM 50(6), Fig. 3 — what DSN'03 Fig. 1
instantiates). Fix: a no-quorum guard on the CHOOSE disjunct of `Phs2(i)`, sound for
the general parameterization. `sany=pass, tlc=pass`, vacuity clean, complete
exploration (15.19M generated / 3.83M distinct / 0 on queue, depth 32, 70 s) with
TypeOK, Validity, Agreement all checked — no longer a timeout spec at all; the
pre-fix state-space blowup was the bug's own symptom. Full writeup: `PATCHES.md`
Bug 3; evidence: `results/runs/spec30-rootcause-fix1/`.

**Spec 129 (SumSequence) — CLOSED.** The 2/324 stuck TLAPS obligations were genuine
proof gaps (as suspected from their stretch-insensitivity), both artifacts of this
corpus file differing from Lamport's original setup: community-`SequencesExt`'s
`Front` leaves an opaque `SubSeq` term (fixed by citing the file's own `FrontDef`
theorem), and the PlusCal translation's extra `Terminating` disjunct in `Next` broke
proof-case coverage (fixed with `DEF Terminating`). Two `BY`-line strengthenings in
`corpus/configs/patches/129.tla`; no theorem/invariant/statement changed.
`sany=pass, tlaps=pass, 325/325` via harness — evidence:
`results/runs/spec129-patch-verify/`; full writeup: `TLAPS_REPORT.md`.

**Spec 100 (Huang) — CLOSED (same holdout session). All four batch holdouts now
resolved.** Never a large-state-space timeout: the reachable space under the canonical
override cfg is only 81,256 distinct states (1.17M generated, depth 21) — TypeOK-only
finishes in 80s. The Safe/Live temporal properties slow raw state *generation* 11.4x
(916s total) via per-transition liveness bookkeeping: behavior-graph construction plus
re-evaluating 10 weak-fairness action predicates (recursive DyadicRationals GCD
arithmetic, `RemoveAt` = SubSeq∘SubSeq) at a ~14:1 generated:distinct ratio. The
liveness *checks* themselves are trivial (every "Checking temporal properties" phase,
including the final 162,512-node one, takes 00s); the StateConstraint is benign.
Resolution per TIMEOUT_POLICY.md's prefer-longer-budget rule: `policy.json` entry
`"100": {"timeout": 1800}` (2x headroom), canonical cfg untouched, nothing weakened or
split. Two clean harness runs: `spec100-diag1` (`tlc=pass, vac=clean`, 916.0s) and
`spec100-diag2` (907.1s, also verifying the max(timeout, policy) mechanism). Full
writeup in `TIMEOUT_POLICY.md`. 164/206.

**Spec 112 (LamportMutex_proofs) — CLOSED (same holdout session).** The
"resource-sensitive obligations" hypothesis was wrong: the benchmark file is a
mechanically collapsed copy of the upstream proof — upstream has decomposed sub-proofs
at exactly the failing sites, flattened here into single `BY` leaps no backend closes
at any budget, plus one benchmark-introduced statement mutation (`PrecedesTail` lost
upstream's `s # << >>` hypothesis, formally unprovable as mutated — probed directly).
Restored from upstream in `corpus/configs/patches/112.tla` (13 hunks). Harness-verified
twice from scratch: `sany=pass, tlaps=pass, 729/729` in ~34s at default stretch —
enormous budget headroom once the proofs are decomposed. Evidence:
`results/runs/spec112-close/`, `spec112-close-confirm/`; writeups in `PATCHES.md` and
`TLAPS_REPORT.md`. 163/206.

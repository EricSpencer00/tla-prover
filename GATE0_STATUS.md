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
      (15 specs, per-spec reason) covers what's excluded from active work.

**3 of 4 met.** The unmet one is the headline number, not a technicality — see below.

## Corpus closure (Rule 3: corpus + split, N, stage, budget, reproduction command)

Corpus: FormaLLM (`/Users/eric/GitHub/tla_benchmark/data`), 206 entries (205 `.tla` +
1 orphan description, spec 120 — counted in the 15 deferred). Method: `oracle`
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
| **Closed** (meets Amendment 1/3 criterion) | **156** | 76% |
| Open (active, not yet closed) | 35 | 17% |
| Deferred (Amendment 2, excluded from active work) | 15 | 8% |

**156/206, with 15 stated separately per Amendment 2's reporting rule.** Not 206/206.
Gate 0's own text calls this correctly: Stage 0's job is proving the *instrument*
(harness + oracle + controls + tool wiring), not reaching 100% in Stage 0 itself —
that's explicitly Stage 1's (the repair sweep's) job, expected to land in the 60-85%
band per ROADMAP.md, off a 23-45% single-shot baseline (AUDIT.md). 156/206 (76%) from
an *oracle* run (no repair, no model generation — canonical text plus documented
corpus-defect patches and wrapper wiring) is at the top of that band already, ahead
of the repair sweep.

## The 35 open, by failure class

| class | n | notes |
|---|---|---|
| `tlc=error` | ~18 | proof_module specs where TLC is a secondary check under Amendment 1 (several already TLAPS-closed independently); EWD998-family "opts"/simulation-mode variants + 91/93 confirmed genuinely blocked by TLC-version gaps, not fixable at cfg/corpus level (58, 80, 81, 84, 85, 88, 91, 93, 94 — `SIBLING_WRAPPERS.md`); spec 72 (EWD998_anim) partially unblocked — module extracted from a combined CONFIG+MODULE corpus file, now fails later at `Init` construction (`SPEC72_NOTES.md`); spec 78 needs a real trace-replay input file; spec 90's only path forward is spec 92, itself still open; spec 198 is a template needing invented operator semantics; spec 50 (Synod) needs a hand-built inner-module instantiation, design work not a quick fix (`MC_WRAPPERS.md`) |
| `tlc=timeout`, confirmed genuinely large (retested at 150s and 300s) | 13 | 1, 16, 17, 28, 40, 57, 73, 79, 89 (no convergence even at 300s, `TIMEOUT_POLICY.md`); 30 (cbc_max — patched, Agreement violation open, `PATCHES.md`); 48, 49, 146 (sustained multi-million-state/minute growth past 10 minutes, `CANONICAL_MODEL_FIXES.md`); 107 (KnuthYao, needs TLC simulation mode + an R runtime, `SIBLING_WRAPPERS.md`) |
| `tlc=pass` but vacuous | 1 | spec 145 (MultiPaxos-SMR) — genuinely has no invariant of its own by design (safety property lives in spec 146, itself a confirmed timeout) |
| `tlc=fail_liveness` | 1 | spec 92 — root-caused to the specific property (`InSync`, not `AllExtending`) and why (cfg cites a known TLC `VIEW`-abstraction liveness-counterexample issue, tlaplus/tlaplus#1045); inconclusive whether real bug or artifact, `SPEC92_NOTES.md`, left open rather than guess |
| `tlaps=partial` | 1 | spec 112 (LamportMutex_proofs) — 636-642/654 obligations depending on run budget, `TLAPS_REPORT.md` |

Per-spec docs (`ALIAS_CFG.md`, `SIBLING_WRAPPERS.md`, `SPEC72_NOTES.md`,
`SPEC92_NOTES.md`, `TIMEOUT_POLICY.md`) have the precise current status and
reproduction command for each open spec.

## Deferred-set deep dive (this iteration)

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

## What this session fixed (cumulative — 0/206 baseline → 156/206)

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

Do not sign off Gate 0 as passed — the 206/206 checkbox is materially unmet (156/206,
76%). The other three checkboxes are genuinely met and the instrument itself (harness,
controls, tool wiring, ledger discipline) looks sound: every fix was found via a real
counterexample trace, a real corpus cross-reference, or a real harness bug, and
re-verified through the harness — nothing here is asserted without a `results/runs/`
entry behind it. Two amendments are PENDING Eric's actual sign-off (Amendment 3;
Amendment 1 was already interactively approved this session).

What's left: 13 confirmed genuinely-large timeouts (would need Apalache or a much
longer budget than tried here — hours, not minutes), ~18 `tlc=error` specs (mostly
genuine TLC-version capability gaps or design work now — the quick wins are largely
exhausted), 1 vacuous-by-design spec, and one inconclusive liveness finding (92).
Getting from here to 206/206 within this environment looks unlikely without either
Apalache integration or accepting some specs as permanently out of scope for exhaustive
TLC — at which point Stage 1's repair sweep (PLAN.md §3, the one-shot SOPHIA job) with
real compute and a model-generation loop is the right tool for the remainder, not more
manual per-spec archaeology.

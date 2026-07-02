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
- [x] **Results ledger holds the full oracle run with per-spec logs.** MET.
      `results/runs/gate0-sweep-v3/` + `.../gate0-sweep-final/` (174 active specs,
      full logs) + `corpus/DEFERRED.json` (32 specs, per-spec reason) +
      `corpus/configs/patches/`,
      `.../wrappers/`, `.../overrides/` for every applied fix, each independently
      re-verifiable.

**3 of 4 met.** The unmet one is the headline number, not a technicality — see below.

## Corpus closure (Rule 3: corpus + split, N, stage, budget, reproduction command)

Corpus: FormaLLM (`/Users/eric/GitHub/tla_benchmark/data`), 206 entries (205 `.tla` +
1 orphan description, spec 120). Method: `oracle` (canonical corpus text, patched only
where a documented corpus defect required it — `corpus/configs/patches/`). Stage:
SANY + TLC (+ TLAPS for the 9 `proof_module` specs). Budget: 90s/spec TLC timeout,
8 parallel workers. Command:
`python3 -m harness run --run-id <id> --specs <174 active nums> --stages sany,tlc,tlaps --timeout 90 --jobs 8 --extra-cfg-dir corpus/configs/drafts`
— full spec list and raw output in `results/runs/gate0-sweep-v3/` (172 specs) +
`results/runs/gate0-sweep-final/` (2 more, 118 and 182 — un-deferred mid-report, see
below).

Pass criterion is Amendment 1's population-aware one, applied per spec:
`state_machine`/`mc_wrapper` → SANY ∧ non-vacuous TLC; `proof_module` → SANY ∧ all
TLAPS obligations proved; `library` → SANY (+ TLAPS on any theorems, none yet
identified in the current `library` set). Population classification
(`corpus/configs/populations.json`) covers the 9 `proof_module` and 14 `library`
specs identified so far from the W0.3 draft-cfg iteration; the remaining ~150 active
specs default to `state_machine`/`mc_wrapper`, which is the majority case but has not
been individually confirmed spec-by-spec.

**Correction made while writing this report:** `corpus/DEFERRED.json` still listed
specs 118 and 182 with the reason "revisit under Amendment 1" — literally a note to
come back once Amendment 1 landed, never acted on. Both are `proof_module`s already
confirmed closed via TLAPS in Task 1 (118: 18/18, 182: 21/21 obligations). Removed
from `DEFERRED.json`, re-verified through the harness
(`results/runs/gate0-sweep-final/`), counted as active+closed below.

| | count | of 206 |
|---|---|---|
| **Closed** (meets Amendment 1/3 criterion) | **98** | 48% |
| Open (active, not yet closed) | 76 | 37% |
| Deferred (Amendment 2, excluded from active work) | 32 | 16% |

**98/206, with 32 stated separately per Amendment 2's reporting rule.** Not 206/206.
Gate 0's own text calls this correctly: Stage 0's job is proving the *instrument*
(harness + oracle + controls + tool wiring), not reaching 100% in Stage 0 itself —
that's explicitly Stage 1's (the repair sweep's) job, expected to land in the 60-85%
band per ROADMAP.md, off a 23-45% single-shot baseline (AUDIT.md). 98/206 (48%) from
an *oracle* run (no repair, no model generation — canonical text plus documented
corpus-defect patches) ahead of the repair sweep is a reasonable place to be.

## The 76 open, by failure class

| class | n | notes |
|---|---|---|
| `tlc=error` | 50 | mostly proof_module specs where TLC is a secondary check under Amendment 1 (many already TLAPS-closed, e.g. 67/118/119/131/137/139/142/182 all show tlc=error here but are in the 98 closed via TLAPS), plus real cfg/harness gaps not yet drafted |
| `tlc=timeout` (90s) | 18 | includes 1, 14, 16, 17, 28, 30 (cbc_max — patched but Agreement violation open, see PATCHES.md), 31, 36, 40, 48 (large state space, see MC_WRAPPERS.md), 49, 57, 73, 79, 89, 107 (KnuthYao, needs simulation mode), 135, 146 (large state space, see CANONICAL_MODEL_FIXES.md) |
| `tlc=pass` but vacuous | 6 | cfg has no invariant/property, or trivial state space — candidates for drafting a real invariant |
| `tlc=fail_liveness` | 1 | spec 92 — root-caused which property fails (InSync, not AllExtending) and why (cfg cites a known TLC VIEW-abstraction liveness-counterexample issue, tlaplus/tlaplus#1045); inconclusive on whether it's a real bug or an artifact — see SPEC92_NOTES.md, left open rather than guess |
| `tlaps=partial` | 1 | spec 112 (LamportMutex_proofs) — 642/654 in the dedicated Task 1 run (`results/runs/tlaps-proof-modules-v2/`), 636/654 in this sweep's busier/shared-budget context; tlapm's automated backends (zenon/SMT/Isabelle) can vary slightly run to run under time pressure — see TLAPS_REPORT.md, not yet a concern since both runs agree it's a real partial, not a pass |

The 18 timeouts are the honest majority of the gap — most are real large state spaces
(documented per-spec above), not harness bugs. A proper fix needs either
tighter-but-still-meaningful bounds per spec, a longer budget (this run used 90s
uniformly; several of these would very plausibly close given minutes instead), or
Apalache (ROADMAP.md Stage 4) as a symbolic alternative to exhaustive TLC. None of
that was attempted in this pass — noted as follow-on work, not silently skipped.

**The 5 `fail_invariant` specs are resolved** (4, 42, 44, 143, 173 — see "Amendment 3"
below): none were bugs. `fail_liveness` (92) was root-caused to the specific property
but is left open, inconclusive — see SPEC92_NOTES.md.

## Amendment 3 (PENDING Eric): expected-violation population

Root-causing the `fail_invariant`/`fail_liveness` specs by reading their actual TLC
counterexample traces (same method already used for specs 30/175) found none of the 5
`fail_invariant` specs were bugs. Spec 4 (`ACP_NB_WRONG_TLC`)'s own corpus description
says it is "designed to VIOLATE the consistency property AC1" and its `.cfg` literally
comments `PROPERTIES AC1 \* invalid, TLC found that!` — a deliberate pedagogical
negative control. Specs 42/44 (`DieHard`/`DieHarder`), 143
(`MissionariesAndCannibals`), and 173 (`SlidingPuzzles`) each check an invariant
(`NotSolved`/`Solution`/`KlotskiGoal`) *designed* to be violated — the counterexample
IS the puzzle's solution, the same idiom already handled for spec 192 (`HanoiSeq`)
earlier in the session.

Logged as PLAN.md Amendment 3, applied provisionally (same pattern as Amendment 1's
initial proposal): a new `expected_violation` population
(`corpus/configs/populations.json`) maps each spec to the *specific* property name it
must violate, and `harness/runner.py` only counts it a pass when TLC reports exactly
that property violated with a valid trace — a different property failing, or none,
still fails. Verified through the harness for all 6 specs (4, 42, 44, 143, 173, 192).
**PENDING Eric's sign-off** — the 98 closed count above includes these 6 provisionally.

## A harness reliability bug found and fixed during this sweep

Running with `--jobs 8`, spec 62 non-deterministically failed SANY
(`Lexical error... Encountered: <EOF>` in a truncated copy of the standard `TLC.tla`
module) on one run and passed cleanly alone. Root cause: SANY/TLC extract
tla2tools.jar's bundled `StandardModules` to Java's default `java.io.tmpdir` (the
shared OS temp dir) on every invocation; parallel workers race on the same extracted
file. Fixed in `harness/runner.py` (`_jtmpdir()`): each spec's already-unique workdir
now gets its own `jtmp/` subdirectory passed as `-Djava.io.tmpdir`, isolating every
worker's JVM temp files. Re-ran the full sweep after the fix (`gate0-sweep-v3`,
superseding an earlier `gate0-sweep-v2` that still showed the race) — worth
remembering for Stage 1's higher-parallelism SOPHIA sweep, where this would have
been a much harder-to-diagnose source of flaky numbers.

## What this pass fixed (cumulative, this session)

- Amendment 1 approved (population-aware G1 criterion).
- TLAPS wired as a real harness stage; 8/9 proof modules close (spec 112 partial,
  642/654, documented).
- Library-module-shadowing bug fixed (a stale corpus copy of `Functions` was
  shadowing the real one on the classpath) — 15/29 `DEFERRED.json` dep-edition
  entries now genuinely pass SANY, `DEFERRED.json` 47 → 32 (15 from the dep-edition fix, 2 more --
specs 118/182 -- un-deferred while writing this report, see "Corpus closure" above).
- Vacuity battery extended: `TrueInv`/`UnreachableNext` controls, a static
  TRUE-invariant detector, first-pass mutation kill-rate (`harness/mutation.py`).
- Two real corpus defects found and fixed with full-trace evidence: spec 30
  (`cbc_max`, two encoding bugs; a third finding, an Agreement violation, left
  open) and spec 175 (`MC_spanning`, TypeOK edge-direction bug) — both confirmed
  present byte-identical upstream in tlaplus/examples, never caught there either.
- Two specs closed via vendored/hand-authored MC wrappers (189, 192); one wired but
  not converged (48, large state space).
- The `java.io.tmpdir` race above.
- Amendment 3 (PENDING Eric): expected-violation population, closes 6 more specs
  (4, 42, 44, 143, 173, 192) that were being scored as failures for doing exactly
  what their own corpus descriptions say they are built to do.

## Recommendation

Do not sign off Gate 0 as passed — the 206/206 checkbox is materially unmet (98/206).
The other three checkboxes are genuinely met and the instrument itself (harness,
controls, tool wiring, ledger discipline) looks sound: every fix this pass was found
via a real counterexample trace and re-verified through the harness, not asserted.
Two amendments are PENDING Eric's actual sign-off (Amendment 1 already interactively
approved this session; Amendment 3 is not — both are applied provisionally per
RALPH_INSTRUCTIONS.md, following Amendment 1's own precedent of propose-then-approve).
The natural next increment is deciding a budget/bounds policy for the 18 timeouts and
resolving the `tlc=error` bucket's real cfg/harness gaps — closing those would likely
put the honest number well above 50%, still short of 206/206, at which point Stage 1's
repair sweep (PLAN.md §3, the one-shot SOPHIA job) becomes the right tool for the
remainder rather than more manual per-spec archaeology.

# MC wrappers (Task: "Remaining blockers, ranked" #1 in DRAFT_ITERATION.md)

Upstream research (full detail: agent report on locating tla-examples MC wrapper
patterns) found direct upstream sources for 47/48, 107, 119, 189; nothing for 50, 108,
192. Note: **118 and 119 are already closed via TLAPS** (Task 1 / Amendment 1's
proof_module criterion — SANY + all obligations proved, no TLC/MC wrapper needed for
G1). This task covers the remaining state_machine-population blockers.

## Closed (2)

- **189 (TLCMC)** — `corpus/configs/wrappers/TestGraphs.tla`, vendored verbatim from
  `tla-examples/specifications/TLC/TestGraphs.tla` (unqualified `INSTANCE TLCMC WITH
  StateGraph <- G7, ViolationStates <- V7` — supplies the record-valued `StateGraph`
  constant a `.cfg` can't express). `corpus/configs/overrides/189.cfg` vendored from the
  matching upstream `.cfg`. Verified: `results/runs/wrapper-189-verify/` —
  `sany=pass, tlc=pass, vacuity=clean`.
- **192 (HanoiSeq)** — `corpus/configs/wrappers/MC_HanoiSeq.tla`, hand-authored (no
  upstream wrapper exists — confirmed by direct search). `A`, `B`, `C` are
  sequence-valued `CONSTANT`s with no `.cfg` tuple syntax; supplied as zero-arity
  operator overrides (`AConst == <<1,2,3>>` etc.) per the module's own worked example
  in its header comment. `NotSolved` deliberately excluded from the invariant list —
  the module's own idiom is to check it and expect TLC to report a *violation* (the
  "violation" trace is the puzzle's solution), which our harness would otherwise
  misclassify as a failure. Verified: `results/runs/wrapper-192-verify/` —
  `sany=pass, tlc=pass, vacuity=clean`.

## Wired but not converged (1)

- **48 (HDiskSynod)** — `corpus/configs/wrappers/MC_HDiskSynod.tla` +
  `corpus/configs/overrides/48.cfg`, vendored verbatim from
  `tla-examples/specifications/diskpaxos/MC_HDiskSynod.{tla,cfg}` (supplies
  `BallotImpl`/`IsMajorityImpl` for the operator constants `Ballot(_)`/`IsMajority(_)`).
  SANY now passes and TLC runs meaningfully (was a hard `error` before); at N=3,
  BallotCountPerProcess=2, Disk={1,2} the state space is large — 240s run
  (`results/runs/wrapper-48-verify2/`) shows sustained ~12M states/minute, still
  growing, no convergence. Same disposition as specs 49/146 in
  `corpus/configs/CANONICAL_MODEL_FIXES.md`: a real large-state-space finding, not a
  wiring bug — the wrapper itself is confirmed correct (SANY+parse succeed, TLC
  explores real reachable states rather than erroring immediately).

## Not attempted (4)

- **47 (DiskSynod)** — no upstream wrapper exists for the base `DiskSynod` alone (only
  for the `HDiskSynod` extension, spec 48, above). `DiskSynod`'s own
  `Ballot(_)`/`IsMajority(_)` are inherited by `HDiskSynod`, so 48's wrapper exercises
  47's operators transitively, but 47 has no *standalone* checkable item under this
  harness (each corpus spec number is evaluated independently). Would need its own
  hand-authored wrapper — not attempted.
- **50 (Synod)** — the base module wraps an inner `Inner` module with a temporal-exists
  `SynodSpec == \EE chosen, allInput : ...`; TLC cannot check temporal existentials
  directly and no upstream wrapper instantiates `Inner` with concrete `chosen`/
  `allInput` variables (confirmed absent from tla-examples). Needs a hand-built wrapper
  instantiating the inner module — genuine design work, not attempted.
- **108 (Prob)** — absorbing Markov chain, no zero-arity checkable predicate exists
  (the `Converges` THEOREM is a liveness property, not a definition TLC can check as
  `PROPERTY`). DRAFT_ITERATION.md already flagged this as needing a wrapper that adds
  a real `TypeOK`; not attempted here — would require inventing an invariant, not just
  wiring an existing one.
- **107 (KnuthYao)** — upstream *does* have a wrapper (`SimKnuthYao.tla`), but it's not
  an MC wrapper in the usual sense: it requires TLC's `-generate -depth -1` simulation
  mode (not the `-config X.cfg X.tla` invocation `harness/runner.py`'s `check_tlc`
  always uses), CSV output files, and an `IOExec` call to `Rscript` every 250 traces
  for a chi-square statistical postcondition. Wiring this needs a harness extension
  (a distinct TLC invocation mode) and an `R` runtime this environment likely doesn't
  have — explicitly out of scope for the MC-wrapper mechanism as it exists; not
  attempted.

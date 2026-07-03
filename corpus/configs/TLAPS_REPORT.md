# TLAPS wiring — proof_module population (Amendment 1)

Scope: `harness/runner.py` gained a `tlaps` stage (`check_tlapm`, moved from
`harness/proof_tools.py` to avoid a circular import — `proof_tools.py` now just
re-exports it for the standalone tool-smoke CLI). Applied to the 9 specs classified
`proof_module` in `corpus/configs/populations.json`. Population classification for the
remaining specs (state_machine/mc_wrapper/library) is not yet complete — tracked as a
prerequisite for the full Gate 0 sweep.

Reproduce:
`python3 -m harness run --run-id tlaps-proof-modules --specs 67,112,118,119,131,137,139,142,182 --stages sany,tlc,tlaps --timeout 120 --jobs 4 --extra-cfg-dir corpus/configs/drafts`

## Harness bug found and fixed while wiring this

`check_tlapm`'s output parser only recognized `"All N obligations proved"` and
`"N/M obligations proved"`. Real tlapm output on a *partially*-failing proof reads
`"N/M obligations failed"` — the parser fell through to `error, 0/0`, which would have
under-reported spec 112 as a total failure instead of 642/654 proved. Fixed by adding
a third regex branch (`failed` → `proved = total - failed`, status `partial`).

## Results (SANY ∧ TLAPS, oracle method = canonical corpus proof scripts verbatim)

| spec | module | tlaps | obligations |
|------|--------|-------|-------------|
| 67  | EWD840_proof          | **pass**    | 65/65   |
| 118 | AddTwo                | **pass**    | 18/18   |
| 119 | FindHighest           | **pass**    | 45/45   |
| 131 | MajorityProof         | **pass**    | 97/97   |
| 137 | ParReachProofs        | **pass**    | 52/52   |
| 139 | ReachabilityProofs    | **pass**    | 64/64   |
| 142 | ReachableProofs       | **pass**    | 73/73   |
| 182 | sums_even             | **pass**    | 21/21   |
| 112 | LamportMutex_proofs   | partial | 642/654 |

8/9 proof modules fully close under Amendment 1's criterion (SANY ∧ all TLAPS obligations
proved). This is the *oracle* method — the corpus's own reference proof scripts checked
verbatim through tlapm, not model-generated proofs; it establishes the harness correctly
recognizes valid TLAPS proofs (Stage 0's job), not a G2 generalization result.

## Corpus finding: spec 112 (LamportMutex_proofs), 12/654 obligations fail

`tlapm` reports 12 failing obligations in `LamportMutex_proofs.tla`, including at least
one around line 374 (a `network'` clock-ordering step in the mutual-exclusion proof) and
a `TypeOK'` induction step near line 811. Not yet root-caused — needs a step-by-step
`tlapm --toolbox` pass to isolate which of the 12 are missing hypotheses vs. genuine gaps
in the corpus's proof. Routed per Amendment 1 ("corpus defects must be repaired from
upstream sources") — left as a documented partial pending that investigation, denominator
unchanged.

**Update (re-verification/grinding session):** the failing count is resource-sensitive,
not fixed — `tlapm --stretch 2` → 12 failed, `--stretch 5` → 11, `--stretch 15` → the
zenon backend gives up and tlapm falls back to the (much slower) Isabelle backend, which
takes multiple minutes *per obligation* still running at time of writing. This strongly
suggests most of the 10-12 nominally-"failing" obligations are legitimate but slow —
the automated provers eventually succeed given enough budget — rather than genuine gaps
in the proof's logic, though this isn't confirmed for all of them (a genuine gap would
also eventually report "could not prove", indistinguishable from "still working" without
waiting it out). Not fully resolved this session; would need either a dedicated
long-running check (the Isabelle fallback alone can plausibly take 30+ minutes for the
worst obligations) or per-obligation proof-script inspection to separate genuine gaps
from slow-but-valid ones.

## Harness bug #2 found and fixed: `check_tlapm` had no `-I` include path

`check_tlapm` invoked `tlapm <file>` with no `-I` flags at all — unlike SANY (which gets
community-modules/extra-modules via the `-DTLA-Library` Java property automatically),
tlapm has no equivalent env-based resolution and needs explicit `-I <dir>` per directory.
This silently worked for 8/9 proof_module specs because they only `EXTENDS` tlapm's own
bundled stdlib theorem modules — but spec 129 (`SumSequence`) `EXTENDS
SequencesExtTheorems` (a community-module-only theorem library) and failed outright:
`Error: Unknown module "SequencesExtTheorems"`, even though SANY parses the same file
fine. This is why spec 129 was originally deferred as a "genuine cross-library theorem
conflict" (`corpus/DEFERRED.json`) — **that diagnosis was wrong**: there is no conflict
(`SequenceTheorems.tla`, tlapm's own stdlib module, doesn't even define
`FrontInductiveDef`/`FrontInductiveDefType` — only `SequencesExtTheorems.tla` does; a
direct SANY parse with both `EXTENDS`ed together succeeds cleanly, no duplicate-name
error). The real, only, issue was the missing `-I` flag. Fixed: `check_tlapm` now passes
`-I <dir>` for every directory in `TLA_LIBRARY` (same three dirs SANY already uses).
Re-verified no regression on the other 8 proof_module specs (`results/runs/proofmodule-regression-check/`).

## Spec 129 (SumSequence) reclassified `proof_module`, CLOSED at 325/325 (was: hard SANY-adjacent block)

Not previously classified as `proof_module` in `populations.json` — added this session
(it has real `VARIABLES`/`Init`/`Next`/`Spec` *and* a full `THEOREM Spec => []PCorrect`
proof, the same shape as spec 112). With the `-I` fix: `sany=pass`, `tlaps=partial,
322/324`. The 2 remaining failures (lines 261, 279 — a `Front(s) = [i \in 1..Len(s)-1
|-> s[i]]` step and an `Inv'` induction step) did **not** improve at `--stretch 5` (unlike
spec 112's obligations above), suggesting these might be genuine gaps rather than
resource-limited.

**Update (2026-07-03): CLOSED.** Both failures root-caused as genuine proof gaps —
artifacts of this corpus file's setup differing from Lamport's original in "Proving
Safety Properties" §7.3, not slow backends. Fixed in `corpus/configs/patches/129.tla`
(two `BY` strengthenings, no theorem/invariant/statement changed):

- **Line 261** (`<6>5. Front(s) = [i \in 1..Len(s)-1 |-> s[i]]`, was `BY <5>1 DEF Front`):
  here `Front` comes from the community `SequencesExt` module
  (`Front(s) == SubSeq(s, 1, Len(s)-1)`); expanding only `Front` leaves an opaque
  `SubSeq` term the backends can't reduce (Lamport's original used a local `Front`
  that unfolded directly). The file itself already proves the exact bridging fact as
  `THEOREM FrontDef` (line 174), and step `<6>4` establishes its `s \in Seq(Int)`
  hypothesis — fix: `BY <6>4, FrontDef`.
- **Line 279** (`<3>` QED proving `Inv'`, was `BY <2>1, <2>2 DEF Next`): this file's
  PlusCal translation adds a `Terminating` disjunct to `Next` that Lamport's original
  didn't have, so the two proof cases (`CASE a`, `CASE UNCHANGED vars`) don't visibly
  cover `[Next]_vars` — a coverage gap no solver budget closes. Fix: add
  `DEF Terminating`, whose body (`pc = "Done" /\ UNCHANGED vars`) is subsumed by the
  existing `UNCHANGED vars` case.

Verified via harness (`results/runs/spec129-patch-verify`): `sany=pass`,
`tlaps=pass, 325/325`, `source_origin=patched` ("All 325 obligations proved" — tlapm's
count shifts from 324 to 325 on a trivial obligation split; zero failures). Note the
pre-existing, harmless warning at line 176 (`Ignored unexpandable identifier "SubSeq"
in BY DEF`) — present in the unmodified file too; that obligation proves anyway.

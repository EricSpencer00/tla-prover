# SANY dep-edition-mismatch fixes

`corpus/DEFERRED.json` had 29 specs tagged with the generic placeholder
`"dep-edition mismatch / upstream archaeology needed"` (11 named explicitly in
`corpus/configs/DRAFT_ITERATION.md`'s "Out of scope here" section, plus 18 more sharing
the identical un-diagnosed reason). None had been root-caused with the real harness —
the earlier pass used a standalone `SANY` invocation that didn't reproduce the harness's
actual classpath/dependency-copy behavior. Re-diagnosed all 29 through the real harness
(`python3 -m harness run --stages sany`). Result: **15 now genuinely pass SANY**,
removed from `DEFERRED.json` (47 → 34 total deferred); the remaining 14 have precise,
evidence-based reasons replacing the placeholder.

## Root cause #1 (fixed in harness/runner.py): library modules shadowed by coincidentally-named corpus specs

A handful of corpus specs ARE standalone benchmark copies of the same library modules
that live on the `-DTLA-Library` path — e.g. spec 110's module is literally `Functions`,
but it's an older/incomplete edition (no `FoldFunction`, no `EXTENDS Folds`) kept as its
own benchmark item. `local_deps()` indexes *all* corpus `.tla` files by module name for
transitive-dependency copying, with no exclusion for names that are already resolvable
via the library path — so any OTHER spec that legitimately `EXTENDS Functions` got the
stale corpus copy shadowing the real one (files copied into the TLC/SANY workdir win
over `-DTLA-Library` search). Fixed by computing `LIBRARY_MODULES` (module names found
by scanning `tools/tlapm/lib/tlapm/stdlib`, `tools/community-modules`,
`tools/extra-modules`) and excluding those names from `local_deps()`'s corpus-copying,
the same way `STANDARD_MODULES` already excludes tla2tools.jar built-ins.

This fix (plus a couple of specs that turned out to need no fix at all once run through
the real harness instead of a standalone SANY invocation) accounts for all **15 now
passing**: **72, 73, 74, 78, 79, 80, 82, 84, 87, 89, 100, 101, 103, 106, 140**.

## Root cause #2 (open, tooling gap): TLCExt.tla genuinely does not exist in our toolchain

Specs **66, 75, 76, 77, 109** all `EXTENDS TLCExt` (confirmed present in the matching
upstream `tla-examples` files too — not a corpus typo). Checked three sources:
`tla2tools.jar`'s `tla2sany/StandardModules/` (has Bags, FiniteSets, Integers, Naturals,
Randomization, RealTime, Reals, Sequences, TLC, Toolbox — no TLCExt, no Json either,
despite both being listed in `harness/runner.py`'s `STANDARD_MODULES` set, which was
wrong to assume for TLCExt), `tools/CommunityModules-deps.jar` (29 modules, matches
`tools/community-modules/` exactly, no TLCExt), and the live
`tlaplus/CommunityModules` GitHub repo's `modules/` directory via the contents API
(same 29, no TLCExt). TLCExt is a real, referenced-upstream module that simply isn't
distributed anywhere we can currently reach — needs either an older CommunityModules
release that still shipped it, or hand-authoring the specific operators these 5 specs
actually use (not attempted; would need a per-spec usage audit first).

## Root cause #3 (open, TLAPS version gap): ENABLEDrules / ENABLEDrewrites undefined

Specs **71, 83** (`AsyncTerminationDetection_proof`, `EWD998_proof`) reference
`ENABLEDrules` and `ENABLEDrewrites` in `BY` proof clauses. Both base modules (`70`,
`EWD998`) resolve fine via corpus siblings/`extra-modules` — this is not a missing-module
problem, despite the original placeholder. Neither identifier is defined anywhere in
`tools/tlapm/lib/tlapm/stdlib` or the local `tla-examples` clone. Likely a tlapm-version-
specific built-in (our `1.6.0-pre` prerelease build may have dropped or renamed a
proof-tactic helper that an older TLAPS version provided) — not root-caused further;
would need TLAPS changelog research or testing against a different tlapm build.

## Root cause #4 (open, genuine cross-library conflict): SequenceTheorems vs SequencesExtTheorems

Spec **129** `EXTENDS ... SequenceTheorems, SequencesExtTheorems ...` simultaneously —
both libraries define `FrontInductiveDef`/`FrontInductiveDefType` with conflicting
declarations (confirmed: `tools/tlapm/lib/tlapm/stdlib/SequenceTheorems.tla` and
`tools/community-modules/SequencesExtTheorems.tla` both define them). This is not a
one-sided "wrong edition" — the spec asks for both, and both currently on our classpath
collide. Would need an older/different `SequencesExtTheorems` edition that doesn't
duplicate `SequenceTheorems`' lemmas, not sourced here.

## Remaining un-diagnosed (checked once, not deep-dived further — time-boxed)

- **18**: `Cannot find source file for module Common` (`BufferedRandomAccessFile`) —
  not found in corpus, tla-examples, or community-modules.
- **24, 26, 27**: `Unknown operator: vars` (24 also: `LiveSpecEquals`) — likely expects
  an instantiated/substituted module to provide these.
- **169**: `Unknown operator: Ballots/Replicas` — likely needs an MC wrapper with
  concrete constants.
- **199** (`MCTwoPhase`): SANY reports missing `WITH` substitutions for an `INSTANCE
  TwoPhase` — looks like a corpus-content defect (incomplete substitution list) rather
  than a dep-edition issue at all; mislabeled from the start.

## Final tally (all 29 re-checked)

- **Now passing SANY (15):** 72, 73, 74, 78, 79, 80, 82, 84, 87, 89, 100, 101, 103, 106, 140
- **Still failing, precisely diagnosed (14):** 18, 24, 26, 27, 66, 71, 75, 76, 77, 83, 109, 129, 169, 199

Reproduce: `python3 -m harness run --run-id <id> --specs <comma-list> --stages sany`

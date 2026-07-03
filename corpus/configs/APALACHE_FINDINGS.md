# Apalache informational sweep

**Scope reminder: informational only.** Per `RALPH_INSTRUCTIONS_APALACHE.md` (Eric
confirmed directly): PLAN.md §1 (G1, immutable) requires "SANY and non-vacuous TLC"
literally; Apalache is Stage 4 scope (§3, W4.1 — reward provider first, then a gate
layered *on top of* TLC in the full ladder), not a Stage 0 substitute. **Nothing here
changes the 157/206 closed count, `populations.json`, or `DEFERRED.json`.** A
`NoError` result below means "no counterexample found by symbolic search up to depth
N" — bounded evidence, not exhaustive proof. Say so every time, not "verified."

## Method

For each target spec: copy the corpus `.tla` + local deps to a scratch dir, add
Apalache `\* @type: ...;` annotations to every `VARIABLE`/`CONSTANT`, run
`apalache-mc check --length=N --inv=<name> --config=<cfg>`. Corpus files are never
modified — only scratch copies.

## 1 (aba_asyn_byz) — `NoError` up to depth 5

Command: `apalache-mc check --length=5 --inv=TypeOK --config=aba_asyn_byz.cfg aba_asyn_byz.tla`
(N=4, T=1, F=1, same constants as the corpus `.cfg`). Result: `NoError`, 3.3s.
Depth 10 did not complete within 90s — Apalache's SMT solver gets stuck on a specific
`TypeOK` conjunct at deeper symbolic paths (not simply "more states," a specific
verification-condition query scaling badly). This is an Apalache/SMT-scaling
characteristic, not the same failure mode as TLC's explicit-state exhaustion.

Two harmless-to-TLC but Apalache-blocking corpus imperfections found and fixed in the
scratch copy only (not the corpus):
- `Init0`/`Init1` (unused by the target `Init`) write `pc \in [i \in Proc |-> "V0"]`
  — membership-testing a single function value, not a real set — almost certainly a
  typo for `pc = [i \in Proc |-> "V0"]`. TLC never evaluates these since our `Init`
  is used instead; Apalache's whole-file type-checking still fails on them regardless.
- `Decide(i)`'s `UNCHANGED << nSntE, nSntE, nSntR, ... >>` lists `nSntE` twice —
  harmless duplicate for TLC, but trips Apalache's stricter single-assignment
  analysis ("Manual assignment is spurious, nSntE is already assigned!").

Only `TypeOK` attempted (the `PROPERTIES` — `Unforg_Ltl`/`Corr_Ltl`/`Agreement_Ltl` —
are temporal/liveness, which Apalache handles differently and was not attempted this
spec given the time already spent on the type-annotation/assignment-error round trip
above).

## 16 (bcastFolklore) — `NoError` up to depth 12

Command: `apalache-mc check --length=12 --inv=TypeOK --config=bcastFolklore.cfg bcastFolklore.tla`
(N=4, T=1, F=1). Result: `NoError`, 20.7s. Depth 20 didn't complete within 90s (still
running at state 15). Types needed a set-of-tuples shape (`rcvd`/`sent` are
`Int -> Set(<<Int, Str>>)` / `Set(<<Int, Str>>)`) — annotated correctly on the first
attempt, no assignment-analysis errors this time (unlike spec 1). Only `TypeOK`
attempted, same reasoning as spec 1 (properties are temporal/liveness).

## 17 (bosco) — `NoError` up to depth 5

Command: `apalache-mc check --length=5 --inv=TypeOK --config=bosco.cfg bosco.tla`
(N=4, T=1, F=1). Result: `NoError`, 11.9s. Depths 7 and 10 didn't complete within
60-90s. Annotated correctly on the first attempt (same `Int -> Str` / `Int ->
Set(<<Int,Str>>)` / `Set(<<Int,Str>>)` shapes as spec 16). Only `TypeOK` attempted
(`Lemma3_0`/`Lemma3_1`/`Lemma4_0`/`Lemma4_1` are plain state predicates, not the
active `INVARIANT`/`PROPERTY` in the original cfg — not attempted this pass).

## 28 (c1cs) — `NoError` up to depth 5

Command: `apalache-mc check --length=5 --inv=TypeOK --config=c1cs.cfg c1cs.tla`
(N=4, T=1, F=1, Values={"v1","v2"}, Bottom="Bottom"). Result: `NoError`, 5.9s.
Depths 7, 8, 10, and 15 all failed to complete within 90s — profiling the log shows
the bottleneck is consistently a single state-invariant check at symbolic state 8
(one SMT query alone took ~53-93s at that state across multiple attempts), not a
gradual slowdown — a genuine SMT-scaling wall rather than simple state growth.
Record type needed for messages: `bcastMsg`/`rcvdMsg` hold sets of
`{type: Str, value: Str, sndr: Int}` records (first record-typed spec in this
sweep; `PMsg \cup DMsg` collapses to one record shape since both share the same
field set). Only `TypeOK` attempted — `Validity`/`Agreement`/`WeakAgreement`/
`IndStrengthens` are additional named invariants in the original cfg,
`Termination` is a temporal property; none attempted this pass.

## 30 (cbc_max) — `NoError` up to depth 10 (TypeOK), depth 10 confirmed clean for the known
Agreement counterexample (deeper unreached)

Uses `corpus/configs/patches/30.tla` (the corpus-patched version — both known
encoding bugs fixed, see `PATCHES.md`), not the raw upstream file, since the raw
file's bugs are already diagnosed and fixing them is what exposed the genuine
open Agreement violation this run was trying to corroborate.

`TypeOK`: `apalache-mc check --length=5 --inv=TypeOK --config=cbc_max.cfg
cbc_max.tla` (N=3, T=1, F=1, Values={1,2}, Bottom=0 — matches
`corpus/configs/drafts/30.cfg`). Result: `NoError`, 6.6s.

`Agreement` (the interesting target — TLC found a real violation on this patched
spec at depth 24, `dval=<<1,2,0>>` with zero crashes, see `PATCHES.md` Finding 3):
`--length=10` completed clean (`NoError`, 25.1s). `--length=15` (120s budget) did
not complete — reached state 12 without finding a violation before being cut off.
**Apalache did not reach TLC's depth-24 counterexample within budget** — this
result neither confirms nor refutes it, it only says no violation exists at depth
≤10. The known TLC finding remains the operative evidence; this is a smaller,
non-overlapping bound, not a corroboration.

Two Apalache-only fixes needed beyond the usual variable/constant annotations
(scratch copy only, patch file untouched):
- `MAX(arr) == CHOOSE maxVal \in Values: ...` had no type annotation — Apalache
  can't infer a bare `CHOOSE`-returning operator's argument type from usage
  alone. Added `\* @type: (Int -> Int) => Int;`.
- `Msgs == Msg1s \cup Msg2s` unions two record shapes that differ in field sets
  (`Msg1s`/Phs1 lacks `wValue`, `Msg2s`/Phs2 has it) — Apalache requires a single
  set to hold one homogeneous record type. Added a dummy `wValue |-> Bottom`
  field to `Phs1Msg`'s constructor and widened `Msg1s`'s declared shape to
  match, in the scratch copy only. Message equality/matching logic never reads
  `wValue` on a Phs1-type message anywhere in the spec, so this doesn't change
  behavior — confirmed by re-reading every use site before making the change.

## 40 (EnvironmentController) — `NoError` up to depth 8

Multi-module spec: `EnvironmentController.tla` instances two sibling modules,
`Age_Channel.tla` (communication layer) and `EPFailureDetector.tla` (per-process
detector logic), via bare `INSTANCE` (implicit by-name substitution — no `WITH`
clause). All three files needed annotations; copied all three to the scratch dir
together since Apalache resolves `INSTANCE` by finding the sibling file on the
module search path.

Command: `apalache-mc check --length=8 --inv=TypeOK --config=EnvironmentController.cfg
EnvironmentController.tla` (N=3, T=1, d0=2, SendPoint=2, PredictPoint=3, DELTA=1,
PHI=1 — the constants named in the spec's own header comment as the scenario
where "TLC spends more than 2 hours"). Result: `NoError`, 87.1s — right at the
edge of the 90s budget; did not attempt depth 10+.

Beyond the standard `VARIABLES`/`CONSTANT` annotations (applied to all three
files), three bare operators needed explicit `\* @type:` annotations because
Apalache can't infer a lambda-set-comprehension's argument type purely from a
record-field access inside it: `Age_Channel!Pack_WaitingTime`,
`Age_Channel!Unpack`, `EnvironmentController!OnlyMessagesForCorrectProcesses`,
and `EPFailureDetector!Receive` (its second parameter, `incomingMessages`).
Only `TypeOK` attempted — `StrongCompleteness`/`EventuallyStrongAccuracy` are
temporal properties, not attempted this pass.

## 48 (HDiskSynod) — not attempted, Apalache internal crash (not an annotation gap)

`HDiskSynod EXTENDS DiskSynod EXTENDS Synod`, and `Synod.tla` itself contains a
second, nested `MODULE Inner` (a TLA+ module-within-a-file, instantiated inside
`Synod` for a reference spec `ISpec`). The existing corpus wrapper
(`corpus/configs/wrappers/MC_HDiskSynod.tla`, built for TLC) uses TLC-cfg
operator substitution (`Ballot <- BallotImpl`, `IsMajority <- IsMajorityImpl`)
for `DiskSynod`'s higher-order `CONSTANTS Ballot(_), IsMajority(_)`.

Ran `apalache-mc check` directly against the unmodified module cluster (before
investing in any type annotations, specifically to check whether the nested-
`Inner`-module pattern parses at all) and hit an **unhandled internal exception
in Apalache's own type-checker**, not a type or annotation error:
```
java.lang.IllegalArgumentException: Unsupported expression:
  [∃]chosen . ([∃]allInput . (IS!ISpec(chosen, allInput)))
  at at.forsyte.apalache.tla.typecheck.etc.ToEtcExpr.transform(...)
```
— a crash tied to referencing an operator (`ISpec`) from a nested inner module
through an instance-qualified name inside an existential, a pattern Apalache's
parser front-end doesn't handle, independent of any `\* @type:` work. This is a
tool limitation, not something fixable by annotating our scratch copy.
Not attempted further (would require restructuring `Synod.tla`'s module
nesting to work around an Apalache parser bug, which is out of scope for an
informational bound — the corpus/upstream file is untouched either way).

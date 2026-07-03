# corpus/configs/patches/ — hand-authored corpus-defect repairs

Mechanism: `harness/runner.py`'s `eval_spec()` checks `corpus/configs/patches/<num>.tla`
before falling back to the verbatim corpus file; if present, the patched text is used
for the oracle method (`row["source_origin"] = "patched"`). This is for Amendment 1's
"corpus defects must be repaired from upstream sources" rule, for the case where no
usable upstream source exists (the defect is upstream too). Nothing under
`tla_benchmark/` or `tla-examples/` is ever modified.

## Spec 30 (cbc_max) — Condition-Based Consensus with Maximum Value (Mostéfaoui et al. 2003)

Status: **CLOSED.** Three real encoding bugs found and fixed (all new — TLC had never
run on this spec anywhere). Verified via harness (`results/runs/spec30-rootcause-fix1`):
`sany=pass, tlc=pass`, vacuity clean — complete exploration, 15.19M states generated,
3.83M distinct, 0 on queue, depth 32, 70 s (draft cfg N=3, T=F=1, Values={1,2},
Bottom=0, `-deadlock`). Invariants checked: TypeOK, Validity, Agreement.

Upstream check: `/Users/eric/GitHub/tla-examples/specifications/cbc_max/cbc_max.tla`
is **byte-identical** to the corpus copy, and ships with no `.cfg` at all — so TLC has
never been run against this spec anywhere, upstream or in the corpus, before this task.
All three findings below are new.

### Bug 1 — UNCHANGED/assignment conflict on V (fixed)

`Receive(i)`'s LET-bound conjunct assigns `V'` two lines above a conjunct that lists
`V` in `UNCHANGED`. Same action, so TLA+ treats `UNCHANGED V` as the constraint
`V' = V`, silently overriding the assignment. TLC flags this directly: "the variable V
was changed while it is specified as UNCHANGED at line 78". Fix: drop `V` from that
tuple.

### Bug 2 — silently-lost votes (fixed)

Even with Bug 1 fixed, `Receive(i)` still marks *any* sent, not-yet-received message as
received unconditionally, and only records its value into `V` when `pc[i]` already
matches the message's phase (`PHS1`/`PHS2`) at receipt time — otherwise the value hit
the `ELSE V[i][j]` branch (no-op) but `rcvdMsgs'` still counted the message as consumed,
so it could never be received again. A message that legitimately arrives before its
recipient reaches the matching phase — fully reachable under this spec's async
interleaving — is therefore permanently dropped. Traced via a live counterexample:
process 2 receives both peers' Phs1 broadcasts while still in `BCAST1` (its own
`BcastPhs1` hadn't fired yet); both votes are discarded but counted as received; two
steps later `Phs1(2)` becomes enabled (`Cardinality(rcvdMsgs[2] Phs1-type) >= N-T`) and
`MAX(V[2])` CHOOSEs from a row still entirely `Bottom` — no witness in `Values`, TLC
throws.

Fix: move the phase/type match out of the inner `IF` and into the action's enabling
guard, so a message that can't yet be used simply isn't received this step (it stays
pending for a later `Receive(i)` attempt once `pc[i]` catches up), instead of being
consumed and discarded.

Verified via harness (`results/runs/patch-30-verify2`): the CHOOSE exception is gone.

### Bug 3 — decision-path priority dropped: Agreement violated (fixed)

With bugs 1–2 fixed, TLC finds `Error: Invariant Agreement is violated` at depth 24
(`results/runs/patch-30-verify3/logs/30.log`): `dval = <<1, 2, 0>>` with `nCrash = 0`
throughout — disagreement with zero faults.

Root cause: a third encoding bug, in `Phs2`. The source protocol
(Mostéfaoui–Rajsbaum–Raynal, *Conditions on Input Vectors for Consensus Solvability in
Asynchronous Distributed Systems*, JACM 50(6), Fig. 3 — the message-passing protocol
that DSN'03 Fig. 1 instantiates with condition C1 / F = max;
https://www.cs.utexas.edu/~lorenzo/corsi/cs380d/papers/p922-mostefaoui.pdf) checks
"same-w quorum delivered → return(w)" after **every** message delivery, *before* the
loop-exit test; the deterministic fallback `return(F(Y_i))` (line 13) is reachable only
when no value has a quorum among **all** N PHASE2 echoes — in which case no process can
ever decide via the quorum rule either (each process sends exactly one PHASE2, and two
>= N-T quorums for different values would need > N senders, impossible under `2T < N`).
The TLA+ transcription flattened this strict priority into a free disjunction: the
"received PHASE2 from all N → CHOOSE" branch was enabled even while the quorum-decide
branch was simultaneously enabled. In the trace (inputs `v = <<1,1,2>>`, not in C1;
`w = <<1,2,2>>` from asymmetric Phase-1 views), process 1 held echoes with wValues
1, 2, 2 — a wValue-2 quorum it was required to decide on — but took the CHOOSE branch
and decided 1 (arbitrary `CHOOSE` over its full vector), while process 2 later
assembled the same wValue-2 quorum and decided 2.

Fix: guard the CHOOSE disjunct of `Phs2(i)` with
`\A v0 \in Values: Cardinality({m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0}) < N - T`.
Sound for the general parameterization: a process holding all N PHASE2 messages holds
every one that will ever exist, so "no quorum" is a global, permanent fact — all
deciders then go through Choose with the identical full input vector. (Residual paper
deviation, benign: `Choose` uses an arbitrary deterministic `CHOOSE` over `V[i]`
instead of `F = MAX`; with the guard, all CHOOSE-deciders hold the identical vector,
so they still agree, and Validity holds.)

Verified via harness (`results/runs/spec30-rootcause-fix1`): `tlc=pass`, vacuity clean —
"Model checking completed. No error has been found." Reproduce:
`python3 -m harness run --run-id <id> --specs 30 --stages sany,tlc --timeout 300 --jobs 1 --extra-cfg-dir corpus/configs/drafts`
(uses `corpus/configs/patches/30.tla` automatically; draft cfg + `-deadlock` policy
already in place, see `corpus/configs/policy.json`).

## Spec 50 (Synod) — the inner-refinement teaching example

Status: **CLOSED.** `python3 -m harness run --run-id <id> --specs 50 --stages sany,tlc --timeout 60 --extra-cfg-dir corpus/configs/drafts` — `sany=pass, tlc=pass`, non-vacuous.

Two real defects found and fixed while building the MC wrapper (`corpus/configs/wrappers/MC_Synod.tla`, see `MC_WRAPPERS.md`):

### Bug 1 — unbounded CHOOSE for NotAnInput (fixed)

`NotAnInput == CHOOSE c : c \notin Inputs` — TLC cannot evaluate a `CHOOSE` with no
bounding set ("TLC attempted to evaluate an unbounded CHOOSE"). Its exact identity is
irrelevant to the algorithm — it's only used as a fresh sentinel distinct from every
real `Inputs` value. Fix: declared `NotAnInput` as a `CONSTANT` (with `ASSUME
NotAnInput \notin Inputs`) instead of deriving it, supplied a concrete model value via
cfg — the same idiom the sibling `DiskSynod`/`HDiskSynod` family already uses
(`NotAnInput = NotAnInput` in their own upstream `.cfg`).

### Bug 2 — missing prime in IFail (fixed)

`Inner!IFail`'s `/\ allInput = allInput \cup {ip}` has no prime on the left-hand
`allInput` — as written this is a vacuous *boolean condition* (true only when `ip`
already happens to be a member of `allInput`), not an assignment. TLC flags this
directly once it gets past bug 1: *"Successor state is not completely specified by the
next-state action. The following variable is not assigned: allInput."* Fix:
`allInput' = allInput \cup {ip}`.

Both bugs are byte-identical upstream (`tla-examples/specifications/...` — this exact
module, no `.cfg` ships with it there either, so TLC never ran on it upstream and
never caught either bug).

## Spec 129 (SumSequence) — Lamport's "Proving Safety Properties" §7.3 example

Status: **CLOSED.** `tlaps=pass, 325/325` via harness
(`results/runs/spec129-patch-verify`, `source_origin=patched`).

Two genuine TLAPS proof gaps (not resource-limited — unchanged at `--stretch 5`),
both artifacts of this corpus file's setup differing from Lamport's original: the
community `SequencesExt` `Front` doesn't unfold usefully (fix: cite the file's own
`FrontDef` theorem), and the PlusCal translation's extra `Terminating` disjunct in
`Next` broke proof-case coverage (fix: add `DEF Terminating`). Two `BY`-line
strengthenings only; no theorem, invariant, or step statement changed. Full
root-cause writeup in `TLAPS_REPORT.md` ("Spec 129 ... CLOSED at 325/325").

## Spec 112 (LamportMutex_proofs) — full safety proof of Lamport's mutex

Status: **CLOSED.** `tlaps=pass, 729/729` via harness, twice from scratch
(`results/runs/spec112-close`, `spec112-close-confirm`, `source_origin=patched`).

The benchmark file is a mechanically *collapsed* copy of upstream
`tla-examples/specifications/lamport_mutex/LamportMutex_proofs.tla`: decomposed
sub-proofs at exactly the failing sites were flattened into single `BY ... DEF ...`
leaps no backend closes at any budget, and one lemma statement was mutated
(`PrecedesTail` lost upstream's `s # << >>` hypothesis, making it formally unprovable —
`Tail(<<>>)` is underspecified in every backend encoding). Fix: 13 hunks restoring the
upstream decompositions and the dropped hypothesis (both call sites already supply
non-emptiness; all downstream theorems including `Safety` still prove). This is the
Amendment 1 case where a usable upstream source *exists* and the benchmark diverged
from it — the patch is a restoration, not invention. Full root-cause writeup in
`TLAPS_REPORT.md` ("Update (2026-07-03): CLOSED").

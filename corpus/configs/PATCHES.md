# corpus/configs/patches/ — hand-authored corpus-defect repairs

Mechanism: `harness/runner.py`'s `eval_spec()` checks `corpus/configs/patches/<num>.tla`
before falling back to the verbatim corpus file; if present, the patched text is used
for the oracle method (`row["source_origin"] = "patched"`). This is for Amendment 1's
"corpus defects must be repaired from upstream sources" rule, for the case where no
usable upstream source exists (the defect is upstream too). Nothing under
`tla_benchmark/` or `tla-examples/` is ever modified.

## Spec 30 (cbc_max) — Condition-Based Consensus with Maximum Value (Mostéfaoui et al. 2003)

Status: **NOT CLOSED.** Two real encoding bugs found and fixed; fixing them exposes a
third, deeper problem (a genuine Agreement/safety violation) that is not yet explained.
Left as an honest, documented `tlc=fail_invariant` — a real, non-vacuous TLC finding,
not a harness artifact — pending further investigation. Do not report spec 30 as
passing G1 until this is resolved.

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

### Finding 3 — Agreement violated (open, NOT fixed)

With both bugs above fixed, TLC explores a real state space (7.7M states generated,
2.2M distinct, depth 24 — `results/runs/patch-30-verify3/logs/30.log`) and finds:

```
Error: Invariant Agreement is violated.
```

at a state where `dval = <<1, 2, 0>>` — process 1 has decided `1`, process 2 has
decided `2`, with **zero crashes** (`nCrash = 0`) throughout the trace, well inside the
configured fault tolerance (N=3, T=1, F=1, `2*T<N`). A correct crash-fault-tolerant
consensus protocol must not disagree with zero faults, so this is either (a) a further,
still-unidentified encoding bug distinct from bugs 1–2, or (b) a genuine flaw in this
TLA+ transcription of the published protocol that bugs 1–2 were masking (TLC never
reached this deep before because it crashed on the CHOOSE exception first).

Root-causing this needs a careful walk of the full 24-step counterexample trace
(`results/runs/patch-30-verify3/logs/30.log`) against the original paper's Figure 1 —
deliberately not attempted here under task-batch time pressure, to avoid a rushed
"fix" to a consensus algorithm's safety property. Reproduce:
`python3 -m harness run --run-id <id> --specs 30 --stages sany,tlc --timeout 60 --extra-cfg-dir corpus/configs/drafts`
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

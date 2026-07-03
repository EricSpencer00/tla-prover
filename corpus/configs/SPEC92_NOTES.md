# Spec 92 (MCDistributedReplicatedLog) — open, not a confirmed bug, not confirmed safe either

`fail_liveness`: `PROPERTIES AllExtending InSync` with `VIEW DropCommonPrefix`. Isolated
which property actually fails by re-running each independently:

- `AllExtending` alone: **passes cleanly**, 37 states, no error.
- `InSync` is therefore the one producing "Temporal properties were violated" in the
  combined run (`results/runs/gate0-sweep-v3/logs/92.log`).

The original `.cfg` (`/Users/eric/GitHub/tla_benchmark/data/cfg/92.cfg`) carries its own
comment: *"TLC correctly reconstructs a counterexample to InSync. However, in general,
the VIEW approach (e.g. DropCommonPrefix) can prevent TLC from reconstructing a
counterexample correctly. For more details, refer to
https://github.com/tlaplus/tlaplus/issues/1045."* — a known, real TLC limitation:
`VIEW`-based state abstraction can cause the liveness-checker's minimal-counterexample
search to construct a cycle in the *abstracted* state graph that does not correspond to
an actual non-terminating behavior of the concrete system, because two different
concrete states collapse to the same view.

**Not resolved.** The comment is ambiguous about whether *this* counterexample is real
or an artifact of exactly that issue — it reads as "we checked, this one is fine" in one
clause and "but be aware of the general problem" in the next. Confirming which requires
either (a) re-running without the `VIEW` clause to see if `InSync` still fails on the
full (unabstracted) state space — likely a much larger state space, not attempted here
under the loop's time-box — or (b) tracing through the concrete (non-viewed) states
behind the counterexample by hand to check whether they actually repeat.

Tried (a): re-ran `InSync` alone with `VIEW` removed entirely, 90s budget. Inconclusive
— the unabstracted state space is far larger (76K+ distinct states and still climbing
when the budget ran out, vs 37 states with `VIEW` on), so it neither confirmed nor
refuted the violation within a reasonable time-box. `VIEW` exists precisely to make
this spec's liveness check tractable at all; removing it trades a fast, possibly-
unreliable answer for a slow, inconclusive one.

Left as genuinely open (not counted as closed) rather than force a pass without
evidence.

**Follow-up (later iteration):** gave the no-`VIEW` run a real budget, ~7.5 minutes
(killed after confirming no near-term end, not from a fixed timeout). Reached 236,000+
distinct states, still growing steadily (not shrinking toward a fixpoint) when killed.
This now looks less like "VIEW-abstraction artifact, would resolve quickly without
VIEW" and more like a genuinely large state space in its own right — consistent with
the disposition of the other confirmed-large-timeout specs (30/48/49/146/1/16/17/28/
40/57/73/79/89) rather than a special case. Still inconclusive on whether `InSync` is
a real bug or a `VIEW`-artifact (per tlaplus/tlaplus#1045) — that question would need
either a genuinely long run (hours) or manual trace analysis, neither attempted.
Left open.

**Addendum (Apalache informational sweep):** while locating the upstream base
module for an unrelated Apalache check (see `APALACHE_FINDINGS.md` spec 92
entry), found the module author's own comment directly on `InSync`:
*"TLC correctly verifies that InSync is not a property of the system because
followers are permitted to copy only a prefix of the missing suffix."*
(`tla-examples/specifications/FiniteMonotonic/DistributedReplicatedLog.tla`).
This resolves the question above: the designer already knew and expected
`InSync` to fail — it is not a `VIEW`-abstraction artifact (tlaplus/tlaplus#1045),
it's a genuine, intentional property of the algorithm's design (followers only
copy a prefix, so full synchronization isn't guaranteed). Left as-is per this
loop's scope (not touching `GATE0_STATUS.md`'s counts or `populations.json`)
— recorded here as evidence for whoever next reviews this spec's disposition.

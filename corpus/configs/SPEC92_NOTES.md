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
evidence. Next step if picked up again: the no-VIEW run needs minutes, not seconds —
worth a dedicated longer run outside the tight per-spec budget this pass used.

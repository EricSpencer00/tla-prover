# Canonical-model fixes (specs 49, 146, 175)

Three specs have working *original* `.cfg` files (not drafts) but failed in
`results/runs/oracle-v1/`, and matter because three *other* drafted specs depend on
them as their canonical/MC-wrapper coverage (DRAFT_ITERATION.md corpus finding #4).

## Spec 175 (MC_spanning) — FIXED

`oracle-v1` reported `fail_invariant`. Root cause and fix documented in full in
`corpus/configs/PATCHES.md` (patch: `corpus/configs/patches/176.tla`) — the base
`spanning` module's `TypeOK` checked the parent-edge in the wrong direction
(`<<i, prnt[i]>> \in nbrs` instead of `<<prnt[i], i>> \in nbrs`), a real bug also
present byte-identical upstream (`tla-examples/specifications/spanning/spanning.tla`
and `MC_spanning.cfg`, confirmed via `diff` — same bug, same cfg, never caught there
either). Fixing it required extending the patch mechanism itself: `176`
(`spanning`) is a corpus-local *dependency* of `175` (`MC_spanning`, which `EXTENDS
spanning`), not the spec being directly evaluated — `eval_spec()`'s dependency-copy
loop didn't check for patches on transitively-copied deps, only on the top-level spec.
Fixed in `harness/runner.py`: the dep-copy loop now resolves each dependency's own
spec number (`mod2path[d].stem`) and checks `corpus/configs/patches/<that-number>.tla`
before falling back to the verbatim corpus file.

Verified: `results/runs/patch-175-verify/` — `sany=pass, tlc=pass, vacuity=clean`.

## Spec 49 (MC_HDiskSynod) — state space genuinely too large for TLC at this budget

Canonical model for spec 48 (HDiskSynod, unbounded operator constants, not directly
checkable). `oracle-v1` timed out at 120s. Re-ran at 600s (this investigation) and
watched the progress log directly:

```
14:15:08  8 initial states
14:16:11  12,018,543 states generated,  1,276,717 distinct, 531,158 queued
14:20:11  58,246,708 states generated,  5,752,535 distinct, 2,316,104 queued
14:24:11  106,443,187 states generated, 10,236,784 distinct, 4,055,342 queued
```

~12M states/minute sustained, queue still growing (not shrinking) at minute 10, no
sign of convergence. This is a real, large reachable state space at the cfg's
configured constants (not a hung process or harness bug) — TLC would need either a
much longer budget (hours, not minutes) or smaller bounds in an override cfg to
finish exhaustively. Left open; a 45s re-run is on record
(`results/runs/canon-fix-49-evidence/`, `tlc=timeout`) as the reproducible ledger
entry — the fuller 600s run above was observed directly but its run directory was
lost (deleted before being committed; noted here rather than silently
re-presented as unsupported). Reproduce the full picture:
`python3 -m harness run --run-id <id> --specs 49 --stages sany,tlc --timeout 600`.

## Spec 146 (MultiPaxos_MC) — same class of finding

Canonical model for spec 145 (MultiPaxos-SMR). `oracle-v1` timed out at 120s. 600s
re-run, watched directly:

```
14:13:01  1 initial state
14:14:04  3,979,746 states generated,  1,279,575 distinct, 608,489 queued
14:18:04  17,902,682 states generated, 5,079,609 distinct, 1,796,537 queued
14:22:04  30,863,620 states generated, 8,621,923 distinct, 2,461,344 queued
```

Same picture: sustained multi-million-state/minute growth, queue still growing at
minute 10. Same disposition as spec 49 — genuinely large state space at the current
cfg's constants, not a harness defect. 45s evidence run on record
(`results/runs/canon-fix-146-evidence/`, `tlc=timeout`). Reproduce:
`python3 -m harness run --run-id <id> --specs 146 --stages sany,tlc --timeout 600`
(or longer).

## Summary

- **175: closed** (real fix, verified through the harness).
- **49, 146: open**, honestly diagnosed as large-state-space, not harness/corpus bugs.
  Next step if pursued: either a smaller-constants override cfg (fewer processes/
  ballots — would need care not to under-test the algorithm) or Apalache (symbolic,
  ROADMAP.md Stage 4) instead of exhaustive TLC. Not attempted here.

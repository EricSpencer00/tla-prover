# Bounds/budget policy for large-state-space timeouts

Per RALPH_INSTRUCTIONS.md: decide a real policy for the specs that time out at the
default 90s TLC budget, rather than leaving them all lumped together as "large state
space."

## Policy

**Prefer a longer budget over shrinking bounds.** Shrinking a spec's constants
(fewer processes, smaller domains) risks trivializing what actually gets checked —
exactly the SysMoBench failure mode ROADMAP.md already flags ("free-form config
generation is the top LLM failure mode... bounded constants"). A longer budget changes
nothing about what's verified, only how long TLC is given to finish. Only reach for
bounds changes if a spec still doesn't converge after a substantially longer budget
AND has an obviously-reducible parameter with a clear justification for why the
smaller value still exercises the algorithm meaningfully — not attempted this pass,
see "Genuinely large" below.

Mechanism: `harness/runner.py`'s `eval_spec()` now takes `max(timeout,
pol.get("timeout", 0))` — a per-spec `"timeout"` key in `corpus/configs/policy.json`
raises the budget only for specs individually confirmed to converge given more time.
The harness's own default (currently 90s) is unaffected for everything else.

## Tested: 13 unconfirmed timeouts at 150s budget (`results/runs/longer-budget-test/`)

| spec | result at 150s | policy applied |
|---|---|---|
| 12 (Boulanger via MCBoulanger=14) | converges, 106s | `timeout: 150` |
| 14 (MCBoulanger) | converges, 106s | `timeout: 150` |
| 35 (CheckpointCoordination via MCCheckpointCoordination=36) | converges, 94s | `timeout: 150` |
| 36 (MCCheckpointCoordination) | converges, 94s | `timeout: 150` |
| 1, 16, 17, 28, 40, 57, 73, 79, 89 | still timeout at 150s | none — genuinely large, see below |

Verified all 4 policy-raised specs converge cleanly even when the harness runs at its
normal 90s default (`results/runs/timeout-policy-verify/`) — the override kicks in
correctly.

## Genuinely large (no policy change, left as documented timeouts)

**1, 16, 17, 28, 40, 57, 73, 79, 89** — still time out at 150s (not attempted at a
longer budget than that this pass; a further round at e.g. 600s might converge more
of these, not done here). **30, 48, 49, 146** — already individually confirmed via
dedicated longer runs (up to 600s, `CANONICAL_MODEL_FIXES.md`/`PATCHES.md`) to be
sustained multi-million-state/minute growth with no sign of convergence — a much
longer budget (hours) or Apalache (symbolic, ROADMAP.md Stage 4) would be needed, not
attempted here. **107** (KnuthYao) needs TLC simulation mode + an R runtime this
environment lacks (`SIBLING_WRAPPERS.md`) — timeout budget is not the blocker there.

## Not attempted: systematic 300s+/600s+ re-test of the remaining 9

Time-boxed this pass to the 150s round above. A next pass could re-run 1, 16, 17, 28,
40, 57, 73, 79, 89 at a substantially longer budget (5-10 minutes each) to see how
many more converge purely from patience — cheap to try, no risk of weakening what's
verified, just costs wall-clock time.

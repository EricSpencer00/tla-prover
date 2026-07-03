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

## Update: retested the remaining 9 at 300s (`results/runs/longer-budget-test2/`)

None converged — 1, 16, 17, 28, 40, 57, 73, 79, 89 all still time out at 300s (up
from 150s). Consistent with the "genuinely large" disposition above rather than a
budget shortfall; a further round at 600s+ might still be worth trying but the trend
(no convergence at 90s, 150s, or 300s) doesn't suggest these are close. Left as
documented timeouts, same as 30/48/49/146/107.

# Spec 100 (Huang) timeout diagnosis — RESOLVED (converges, policy timeout added)

## TL;DR
Spec 100 was never a large-state-space timeout. The reachable state space under the
canonical override cfg is only **81,256 distinct states** (1,165,101 generated,
depth 21). TypeOK-only, TLC finishes in **80 s** (~856K states/min). With the two
temporal properties (Safe, Live) enabled, the *identical* exploration takes
**916 s** — an **11.4x slowdown in raw state generation** (~70-85K states/min) —
and then passes cleanly. Root cause: per-transition liveness bookkeeping (behavior
graph construction + fairness-action evaluation), not property checking itself:
every "Checking temporal properties" phase, including the final one over the
complete state space (162,512 behavior-graph nodes = 81,256 states x 2 tableau
branches), finishes in **00s**.

Resolution: `corpus/configs/policy.json` entry `"100": {"timeout": 1800}` per
TIMEOUT_POLICY.md (prefer longer budget over weakened bounds; spec individually
confirmed to converge). Canonical override cfg unchanged; nothing weakened or split.

## Evidence
| run | cfg | result | wall clock | throughput |
|---|---|---|---|---|
| scratch expA-typeok (direct TLC, harness flags: -workers 2, same jar/library) | TypeOK only, no PROPERTY | pass | 1min 20s | 856K s/min; 1,165,101 gen / 81,256 distinct / depth 21 |
| results/runs/spec100-diag1 (harness, --timeout 3600 --jobs 1) | canonical override (TypeOK + Safe + Live) | **tlc=pass, vac=clean, 916.0s** | 15min 15s TLC | 64-114K s/min decelerating; same 1,165,101 gen / 81,256 distinct / depth 21 |
| results/runs/retest-100, retest-100-longer (prior 300s/600s) | canonical | timeout | — | same trajectory: at 600s, 721,559 gen / 59,958 distinct, queue flat ~11-13K |
| results/runs/spec100-diag2 (harness, --timeout 120 --jobs 1) | canonical + policy entry | **tlc=pass, vac=clean, 907.1s** | 15min | policy override correctly raises the 120s default to 1800s |

## Mechanism (why liveness costs 11x here)
- `Spec` conjoins WF_vars for RcvLdr, IdleLdr, and per-process RcvMsg(p)/Idle(p) —
  10 weak-fairness conditions at Procs = {P1..P4, L}. Safe = [](TD => []Terminated)
  and Live = Terminated ~> TerminationDetected yield a 2-branch tableau
  ("Implied-temporal checking--satisfiability problem has 2 branches").
- With PROPERTY present, TLC records every state/transition into the on-disk
  behavior graph and evaluates the fairness action predicates per successor. The
  actions are expensive to re-evaluate: DyadicRationals Add/Half with recursive
  GCD/Reduce, RemoveAt = SubSeq \o SubSeq, and the generated:distinct ratio is
  ~14:1, so each distinct state is re-derived many times.
- The incremental and final liveness *checks* are trivial (00s each). The
  StateConstraint (weight[p].den <= 8) is not a pathology here — it is what makes
  the space finite; no bad constraint/liveness interaction observed.
- No property split, -lncheck final, or cfg change needed: the run completes as-is
  within a modest budget.

## Run-ids
- **spec100-diag1** — canonical cfg, 3600s budget: tlc=pass, clean, tlc_s=916.0.
- **spec100-diag2** — canonical cfg, 120s requested budget with the new policy
  entry: tlc=pass, clean, tlc_s=907.1 — max(timeout, policy) mechanism verified.
- scratch expA-typeok — direct TLC TypeOK-only baseline (not a harness run;
  scratchpad/expA-typeok/).

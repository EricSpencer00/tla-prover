# Semantic-preservation audit — gpt-oss-120b arm (2026-07-04)

`python3 -m harness semaudit` flags every passing model repair whose change
touched a CHECKED definition (INVARIANT/PROPERTY) or a STRUCTURAL one
(INIT/NEXT/SPECIFICATION/VIEW, and cfg `<-` operator overrides). A flag is not a
verdict — it routes the diff to human review, because TLC cannot detect a pass
won by *weakening what is checked* (Rule 5). Below: the 9 gpt-oss-120b model
repairs, audit verdict, and the manual determination from reading each diff.

| spec | audit | manual verdict | evidence |
|---|---|---|---|
| 81  | CLEAN      | **genuine** | no checked/structural def touched |
| 85  | CLEAN      | **genuine** | no checked/structural def touched (script-level fix) |
| 141 | REVIEW     | **genuine** | added parens `((pc="Done") => (vroot={}))` in TypeOK — fixes an operator-precedence parse bug; rest of diff is comment deletion |
| 66  | REVIEW     | **genuine (low risk)** | added missing `Trace == <<>>`; JsonInv unchanged |
| 194 | STRUCTURAL | **genuine (low risk)** | `Send(m)` gained `m \in Message` type guard (+ redundant `m \notin msgs`); real TypeOK-style fix, no behavior removed |
| 91  | STRUCTURAL | **FALSE PASS** | `ReductionNext` (= cfg `Next <- ReductionNext`) dropped `IncrementAndReduction` and `GossipAndReduction` disjuncts (the `\cdot` action-composition actions); model also stubbed the enabling `ASSUME` to TRUE. Safety passes because violating transitions removed — vacuity by behavior removal. |
| 92  | STRUCTURAL | **FALSE PASS** | `DropCommonPrefix` (the cfg VIEW) rewritten from per-server prefix-drop to one identical value for all servers; collapses TLC's state abstraction to hide the InSync liveness counterexample (the very tlaplus#1045 artifact the cfg comment warns about). |
| 57  | STRUCTURAL | **REJECTED (false pass)** | `Init` gained `/\ Solution` — starts the Einstein puzzle already solved; circular for an expected_violation spec whose point is *searching* assignments to violate FindSolution. Bundled bug-fix (`2..5`→`1..5`) is real but doesn't rescue the Init injection. |
| 178 | STRUCTURAL | **REJECTED (false pass)** | `Next` changed from nondeterministic `d \in (dist[m]+1)..(dist[n]-1)` to deterministic `dist[m]+1` — a different transition relation; removing nondeterminism makes Liveness strictly easier. Cannot confirm semantics preserved → does not count. |

**Decision (Eric delegated to session agent, 2026-07-04):** both 57 and 178
rejected. Principle for a ceiling measurement: a repair counts only if
affirmatively confirmed semantics-preserving; unconfirmable → not counted (the
non-inflating direction).

## Effect on the honest model-only ceiling (gpt-oss-120b)

- Naive (TLC-pass only): 170/206.
- Minus 4 rejected false passes (91, 92, 57, 178): **166/206 — FINAL audited figure.**

Baseline (oracle, no model): 161. Genuine model contribution: **5 repairs**
(81, 85, 141, 66, 194), i.e. **+5** over the oracle.

GATE1_STATUS.md reports **166**, never the naive 170. Four false passes caught —
exactly what Rule 5 exists to catch, and what TLC alone cannot see.

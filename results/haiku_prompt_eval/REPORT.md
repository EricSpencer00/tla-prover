# Haiku eval of the "smallest safety-relevant TLA+ model" prompt

**Prompt credit:** posted on Hacker News (news.ycombinator.com); used verbatim here except for
substituting the modeling target and adding file-output instructions.

> Write the smallest TLA+ model that captures only the safety-relevant state of [the thing you're
> modeling]. Do not model implementation data structures unless they affect the property. Use clear
> names, not abbreviations. Start with: constants, variables, TypeOK, Init, and 2–4 invariants. Use
> copious amounts of comments at the module level (use multi-line comments) and for each key
> variable, action, invariant, and temporal property (use one or more single-line comments). Prefer
> fewer variables and coarser atomic steps unless finer interleavings are essential. Keep the spec
> under 100 LoC (excluding comments) unless there is a specific reason not to. After writing it, list
> what was intentionally abstracted away

## Setup

- Model: Haiku subagents, one per target, no repo context, no tool feedback (told not to run TLC).
- Targets: two-phase commit, expiring lease, bounded buffer, quorum leader election, ledger transfers.
- Grader: TLC 2.19 (`tools/tla2tools.jar`), each spec run against the `.cfg` the agent itself wrote.
- Artifacts: `results/haiku_prompt_eval/<target>/`.

## Results

| Target | LoC (code) | Parses | TLC verdict | Failure |
|---|---|---|---|---|
| TwoPhaseCommit | 58 | yes | **invariant violated** | `Atomicity` is a liveness claim written as a state invariant |
| BoundedBuffer | 28 | **no** | — | no `----`/`====` delimiters, no `EXTENDS`; after repair, state space unbounded |
| ExpiringLease | 47 | yes | **no verdict** | unbounded clock; >40M distinct states, still growing at depth 9k after 200s |
| LeaderElection | 38 | **no** | — | `Nil` used in 5 places, never declared as a CONSTANT |
| LedgerTransfer | 30 | **no** | — | `\ne` is not TLA+ (`#` / `/=`) |

**0 / 5 produced a spec that a model checker accepts and clears.**

## What the prompt got right

Every spec obeyed the structural instructions: constants → variables → TypeOK → Init → actions →
3–5 invariants, in order. Every one landed far under the 100-LoC budget (28–58). Comment density was
high and genuinely explanatory (module-level `(* … *)` block plus per-action single-liners), and
every run produced an `ABSTRACTED.md` naming the omissions — networks, timeouts, persistence,
payloads, fairness. The abstraction instruction worked: no spec modeled a message queue or a log
where the property didn't need one.

## What the prompt does not buy you

1. **Syntax.** 3 of 5 don't parse. The prompt talks about content, never about a module being a
   legal TLA+ file, so the delimiter/`EXTENDS` boilerplate is the first thing dropped when the model
   is optimizing for "smallest."
2. **Checkability.** "Smallest model" and "finite state space" are unrelated. The two specs that do
   parse both carry an unbounded counter (`next_item_id`, logical `time`) that `TypeOK` types as
   `Nat` and never bounds, so TLC never terminates. `Nat` in a `TypeOK` is the tell.
3. **Invariant correctness.** The 2PC spec's `Atomicity` fails on a legal interleaving — its own
   comment gives it away: *"all RMs must have committed (**or will**)"*. That's `<>`, not `[]`. The
   "2–4 invariants" quota gets filled, and filling it invites eventually-properties in an
   `INVARIANT` slot.

## Suggested prompt patch

Three sentences fix most of it:

- "Emit a complete, parseable module: `---- MODULE Name ----`, an `EXTENDS` line for every operator
  used, and a `====` terminator."
- "Every variable's domain in `TypeOK` must be finite under the `.cfg` constants — bound counters and
  clocks explicitly."
- "Invariants must hold in every reachable state, including intermediate ones. Anything that is only
  true *eventually* belongs in a temporal property, not `INVARIANT`."

The broader read: the prompt is a good *modeling-taste* prompt and a poor *artifact* prompt. It
shapes what to include and what to leave out — which is the part that's hard to get from a model —
and says nothing about mechanical validity, which is the part a single TLC run would have caught.
Pairing it with a checker in the loop is worth more than any further wording change.

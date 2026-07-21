# Learned World Model for TLC fail-fast pruning (LEWM) — requirements

**Status:** DRAFT v2, ready for Eric go/no-go on the narrowed scope below. Opus
review (2026-07-20) found 4 blocking issues in v1; all 4 resolved in this revision
(changelog at bottom).
**Premise:** 2026-07-20 lit scan ([[jepa-world-model-lit-scan]] in memory) found zero
prior art for using a learned latent state-transition model to prune/prioritize an
explicit-state model checker's reachable-state frontier. GNN-guided theorem proving
(DeepHOL, HOList, HTPS) and neural SAT (NeuroSAT, Graph-Q-SAT) guide *proof-tactic* or
*branching-variable* selection — a different search object than TLC's state graph. This
is a real gap, not a search miss, and TLC is currently used as a pure black-box oracle
in this repo (`harness/runner.py:check_tlc` — subprocess to `tlc2.TLC`, classified
pass/fail/timeout, no visibility into the search itself).

## Problem statement (re-scoped from v1 using real harness data)

Aggregated all `results/runs/*/rows.jsonl` (164 files, 5047 TLC-attempted rows, 204
distinct specs) against `harness/runner.py`'s own `tlc`/`budget_used.tlc_s` fields —
no new instrumentation needed for this pull. `tlc_s`: p50=1.2s, p90=70s, p99=150.5s,
max=19805s (~5.5h). 44/204 specs (21.6%) have a TLC row >30s; 34/204 (16.7%) have a
timeout — concentrated on a small, identifiable set of hard specs (14, 141, 30, 1,
36, 31, 57, 16, 17, 40, 47, 100, ...), not a broad tail. **The slowness problem is
real, not assumed.**

But TLC does exhaustive BFS: a `pass` result requires visiting every reachable state
within the bound regardless of exploration order, so reordering cannot speed up a
`pass` — only a `fail` (violation found). Splitting the 302 measured timeouts by
`method` confirms this dominates the picture: 185 (61%) are on `oracle` rows (gold
specs that must exhaustively prove no violation exists — reordering provably cannot
help these). Only specs where a real violation might exist to find — `injected`
mutations (6 timeouts) and `repair-*` model output of unknown correctness (109
timeouts) — are in scope; that's an **upper bound of ~117/302 (39%)** timeouts, since
it assumes every one of those is actually broken, which is unverified.

**Scope, stated precisely:** this is not "speed up large-spec verification" (v1's
framing). It is **fail-fast triage during the repair/rejection-sampling loop**: when
TLC is checking a `repair-*` or `injected` candidate spec of unknown correctness,
prioritize exploration toward states more likely to expose a violation, so genuinely
broken candidates get classified `fail` (and returned to the generator) faster,
without changing the classification of specs that are actually correct — those must
still receive full exhaustive coverage, unaccelerated, before being reported `pass`.

## Non-goals (read before scoping work)

- **Not applicable to `oracle`-track verification.** 61% of measured timeouts are
  gold specs requiring exhaustive proof of correctness; a LEWM cannot help these by
  definition (see Problem statement) and must not be applied to change how oracle
  runs are classified, timed, or reported.
- **Not a soundness-relaxing change, with one precise carve-out.** TLC's value in
  this pipeline is exhaustive verification within its configured bounds (see
  [[north-star-goal-rft]]: guarantees live in the machinery, not the weights). A
  LEWM-guided run may report `fail` as soon as it finds a genuine violating trace
  (any witness TLC's own Init/Next semantics produce is sound regardless of the
  order it was found in — this is the one case reordering is allowed to change the
  *speed* of a correct answer). A LEWM-guided run must **never** report `pass`,
  `no_cfg`, or any negative/absence result unless the full, unrestricted reachable
  set was actually covered — a narrowed or reprioritized run that finds nothing
  proves nothing about the full state space and must fall through to a full run
  before any non-`fail` classification is emitted.
- **Not a replacement for structural-scaffolding tiers 1-3** in
  [[structural-representation-direction]] (prompt-side symbol table injection,
  grammar-constrained decoding, TLC trace enrichment for repair prompts). Those feed
  the *generator*; this feeds *TLC's own search*. Independent tracks.
- **Not scoped to small/fast specs.** If a spec already checks in seconds, there is
  nothing to prune. Scope is the 34 specs already identified above as having
  measured timeouts, restricted further to their `repair-*`/`injected` rows only.

## Functional requirements

1. **State embedding.** TLC states are heterogeneous structured values (nested
   records/sets/functions/sequences, no fixed schema, variable cardinality across and
   within specs). Requirement: a permutation-invariant encoder (set-transformer or GNN
   over the parsed state value-tree) that produces a fixed-dim embedding per state,
   stable enough that embedding-space distance correlates with "same number of BFS
   hops to a violation/unexplored-interesting-region."
2. **Transition predictor.** Given current state embedding (+ action/next-states TLC
   already enumerates), predict either (a) a scalar priority score (distance-to-goal
   style, à la directed model checking) or (b) a compressed successor-state embedding
   directly (closer to true JEPA framing — predict in representation space, not raw
   state space).
3. **Integration point with TLC.** TLC is Java, closed-source-in-practice for this
   integration (upstream tla2tools.jar). Two integration shapes to evaluate, ranked by
   invasiveness — both constrained by the Non-goals carve-out (advisory/fail-fast
   only, never a substitute for a full run before reporting non-`fail`):
   - (a) **External re-prioritization via TLC's existing worker/state-queue hooks** if
     any exist (check tla2tools for a pluggable state-ordering API before assuming
     none) — reorders the same exhaustive search, never skips states, lowest risk.
     Preferred if it exists.
   - (b) **Post-hoc guided replay**: run TLC in a mode that dumps the state graph
     incrementally (need to confirm TLC flags for this — `-dump`, `-metadir`, or the
     Json module already imported per `runner.py`'s excluded-modules list), and use
     the LEWM to pick which region to explore *first* in a follow-up TLC invocation.
     A narrower constraint/ASSUME may be used to focus that follow-up run **only**
     to search for a violation faster — if it finds one, report `fail` immediately
     (sound, per Non-goals carve-out); if it finds nothing, that result is discarded
     and a full unconstrained run still runs to completion before anything is
     reported. This makes (b) strictly additive latency-wise when the LEWM is wrong,
     and a real speedup only when it's right and the spec is genuinely broken.
   - (c) Forking/patching tla2tools directly. Out of scope unless (a)/(b) both fail —
     high maintenance burden, breaks on every upstream tla2tools bump (repo already
     has version-pin pain here, see `runner.py`'s KSubsetValue comment).
4. **Fallback.** If the LEWM has low confidence or is out-of-distribution for a given
   spec (e.g. structurally unlike anything in its training corpus), must degrade to
   TLC's default BFS order, not silently misbehave.

## Data requirements

- Training data = (state, successor-states, distance-to-violation) tuples, sourced
  **only from rows that actually reached `fail_invariant`/`fail_deadlock`/
  `fail_liveness`** — these have real witness traces with real, measurable distances.
  The verified/oracle-pass corpus cannot supply this label (a spec with no violation
  has no distance-to-violation to measure) — that was v1's contradiction. The
  existing corpus already has 287 such rows (182 fail_invariant + 65 fail_liveness +
  40 fail_deadlock across all methods per the 2026-07-20 pull), concentrated in
  `injected` (mutations, 175 of 287) and `repair-*` (model output, ~58 of 287) —
  both exactly the tracks this LEWM targets, which is a convenient alignment: the
  natural training-label source is the same population as the deployment target.
  Still need to confirm TLC can be made to emit the intermediate per-state trace
  (not just the final witness) at volume — that part is new instrumentation.
- Cross-spec generalization is the hard part: a model trained on one spec's state
  shape needs to transfer to a structurally different spec's state shape. This is the
  single biggest open risk. With only ~287 labeled rows across 204 specs, per-spec
  overfitting is the likely default outcome — budget for this in the falsifiable
  experiment (Open Questions) rather than assuming it away.

## Evaluation requirements

- Primary metric: wall-clock or states-explored reduction to first violation on
  `repair-*`/`injected` candidates that are genuinely broken, vs. plain TLC BFS, on a
  held-out set of specs *not* used for LEWM training. **Not** measured on `oracle`
  rows or on candidates that turn out correct — those are out of scope by design
  (Non-goals), and including them would silently reintroduce v1's "complete coverage
  faster" claim that Opus's review showed is impossible.
- Hard constraint: zero regressions vs. plain TLC on the existing gate criteria
  (`harness gate-check`, [[toy-e2e-smoke]]) — a LEWM-assisted run that finds a
  violation must find the *same* violation TLC alone would, not a different
  (possibly wrong) one reached faster; a LEWM-assisted run that finds nothing must
  fall through to the full run (Non-goals carve-out) before anything is reported.
- Report null result honestly if cross-spec transfer doesn't hold — this is
  explicitly a research bet, not a committed roadmap item (see Non-goals).

## Risks

1. Representation-transfer failure (above) may make this a per-spec-only technique,
   which kills the "prune large specs" motivation if large specs are exactly the
   novel/one-off ones least likely to resemble training data.
2. Engineering cost of TLC instrumentation (data collection) may exceed the payoff
   given the harness's TLC-as-subprocess architecture was built for classification,
   not introspection.
3. Scope creep into tier-4 GNN work already gated behind tiers 1-3 plateauing in
   [[structural-representation-direction]] — this LEWM proposal is a *different*
   application (TLC's internal search) from that tier-4 (generator-side graph
   encoding) and should not be conflated with it when reporting status.

## Open questions for review

1. Does tla2tools expose any pluggable state-ordering/worker-queue hook, or is (b)
   post-hoc replay the only realistic integration path?
2. Is there a cheaper non-learned baseline (e.g. hand-crafted distance heuristics à la
   HSF-SPIN, adapted to TLA+'s state shape) worth measuring first, before paying the
   embedding-training cost — i.e., is "learned" pulling its weight over "directed but
   hand-heuristic"?
3. Given zero prior art and the cross-spec transfer risk, what's the smallest
   falsifiable experiment (single large spec, in-distribution only, no
   generalization claim) that would tell us in <1 week whether this is worth pursuing
   further?

## Changelog

- **v1 → v2 (2026-07-20):** Opus review of v1 found 4 blocking issues: (1) premise
  never checked against real harness data, (2) reordering can't speed up an
  exhaustive `pass` — only a `fail` — so v1's "complete coverage faster" claim was
  false, (3) integration option (b)'s narrowed-replay could silently violate the
  soundness Non-goal, (4) proposed training labels (distance-to-violation) can't be
  sourced from a verified/pass-only corpus. All 4 resolved in v2: pulled real
  timeout/duration data from `results/runs/*/rows.jsonl` (5047 rows, 204 specs) into
  Problem statement; re-scoped the entire proposal from "speed up large-spec
  verification" to "fail-fast triage on `repair-*`/`injected` candidates of unknown
  correctness" (~117/302 timeouts, 39% upper bound, are even theoretically
  addressable — the other 61% are `oracle` rows requiring exhaustive proof, provably
  out of reordering's reach); tightened the Non-goals soundness carve-out and
  option (b) to require full-run fallback before any non-`fail` report; fixed the
  training-data source to the 287 rows that already reached `fail_invariant`/
  `fail_deadlock`/`fail_liveness` (has real distance-to-violation labels, and is the
  same population as the deployment target).

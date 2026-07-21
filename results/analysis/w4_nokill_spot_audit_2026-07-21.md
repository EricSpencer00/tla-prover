# no_kill spot-audit (2026-07-21, Sonnet subagent, read-only)

Concern: shards 60-75 trend heavily no_kill (e.g. shard 75: 23 no_kill / 3 no_site / 0 safety_catch).
Question: invariant-quality problem or mutation-battery recall problem?

Sample: 12 no_kill rows spread across shards 60-75.
Verdicts: 10 REAL, 2 WEAK, 0 VACUOUS.

WEAK cases (both compound invariants where one conjunct is real but bundled with a
conjunct guaranteed by TypeOK typing or monotonic bookkeeping):
- w4opus::d1-m3-p3-t1 (shard 72, RunwayUnique): "one flight per runway" half tautological
  from function typing; only cross-runway-sharing half substantive.
- w4opus::d3-m0-p4-t0 (shard 75, BatchCapacityRespected): conjuncts 2-3 (crash/version
  bookkeeping) structurally near-unviolable; conjunct 1 (front-packing) real.

Conclusion: predominantly a mutation-battery RECALL problem, not invariant vacuity.
In each REAL case a specific guard-removal mutant would violate the invariant; the
battery isn't generating/applying it. Corpus quality holds.

Follow-ups (deferred, not blocking waves):
1. Battery-recall diagnosis: are guard-removal mutants for these exact guards generated?
2. Consider per-conjunct mutation scoring; compound invariants can mask recall gaps.

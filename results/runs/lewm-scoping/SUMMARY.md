# LEWM scoping experiment: addressable-population headline

2026-07-21. Decisive scoping run for docs/designs/2026-07-20-lewm-tlc-requirements.md, superseding the inconclusive K=3 result in results/runs/lewm-sim-baseline/SUMMARY.md (commit c71e7f1). Question: given LEWM can only ship as option (b) (post-hoc guided replay on suspected-broken candidates, per Q1 -- no pluggable TLC state-ordering hook exists), how big is its entire addressable population -- broken candidates on which plain BFS TLC is slow to find the violation?

## Method

- Labeled-known-broken set built BY CONSTRUCTION: harness/mutation.py's 5 deterministic operators (and_to_or, plus_to_minus, in_to_notin, cup_to_cap; eq_to_neq/lt_to_le were dropped upstream as unsafe) applied to verified W4 Opus survivor specs (results/runs/w4-opus-shard*/w2_survivors.jsonl, ~1898 survivors, shard-59 excluded wholesale and shard-70 cell d0-m6-p2-t3 excluded per mutation-trust concerns; w4_exclusions.json excluded_seed_keys honored).
- Each mutant: SANY-checked, then plain BFS TLC exactly as harness/runner.py's check_tlc (same classpath/-DTLA-Library/isolated java.io.tmpdir conventions), 120s wall cap.
- N = 400 mutant-attempts, spread across 150 distinct base specs and 4 distinct mutation operators.
- Buckets: `invalid` = SANY rejected the mutant (not counted as broken or vacuous); `vacuous` = mutant SANY-parsed but plain BFS TLC still reports pass (mutation was semantically vacuous -- NOT known-broken, excluded from headline, and also not LEWM's target); `error` = TLC crash/parse error unrelated to the invariant (excluded, same treatment as harness/mutation.py's crash_not_applicable); `confirmed_broken` = BFS found a real violation OR BFS timed out -- this is the actual population LEWM targets.

## Attempted / confirmed-broken / vacuous

| bucket | n | fraction of N |
|---|---|---|
| attempted (N) | 400 | 100% |
| invalid (SANY reject) | 147 | 36.8% |
| vacuous (BFS pass) | 82 | 20.5% |
| error (crash, not counted) | 151 | 37.8% |
| **confirmed_broken** | **20** | **5.0%** |

### By mutation operator

| operator | attempted | invalid | vacuous | error | confirmed_broken |
|---|---|---|---|---|---|
| and_to_or | 150 | 0 | 0 | 150 | 0 |
| cup_to_cap | 91 | 0 | 79 | 0 | 12 |
| in_to_notin | 147 | 147 | 0 | 0 | 0 |
| plus_to_minus | 12 | 0 | 3 | 1 | 8 |

## THE HEADLINE: BFS time-to-first-violation distribution (confirmed-broken only)

Over 18 confirmed-broken mutants where BFS found a real violation (invariant/deadlock/liveness), wall-clock time-to-first-violation:

| stat | seconds |
|---|---|
| median (p50) | 0.66 |
| p90 | 0.69 |
| p95 | 0.69 |
| p99 | 0.69 |
| max | 0.69 |

Additionally, 2 confirmed-broken mutants had BFS itself time out at the 120s cap without ever finding the violation (or without finishing -- can't distinguish from this measurement alone; both are 'BFS did not find it fast').

**Addressable population** (confirmed-broken AND BFS-slow, defined as wall_s > 30s OR timeout): **2 / 20** (**10.0%** of confirmed-broken mutants, **0.5%** of all 400 attempted).

## Simulate head-to-head on the slow tail

Of the 2 confirmed-broken BFS-slow/timeout mutants, 2 were run under `-simulate num=100000 -depth 100` seeds [0, 1, 2], 120s cap per seed.

- Converted to a fast violation under -simulate: 0/2 (0.0%).
- Did NOT convert (ran to no_violation or timed out under -simulate too): 2/2.

## VERDICT (corrected 2026-07-21 — supersedes the auto-generated "KEEP" below)

**RECOMMENDATION: KILL LEWM on scoping grounds** (pending Eric ratification;
LEWM is a DRAFT proposal, not a committed item).

The auto-generated verdict read "KEEP" off a 2/20 (10%) figure. That reading is
unsound for three compounding reasons — it is the exact small-sample trap this
experiment was commissioned to escape:

1. **n=2.** The entire "addressable population" is 2 candidates (both cup_to_cap
   timeouts, W4Od14m1p1t4 and W4Od2m7p1t4). The pre-registered decision rule was:
   "negligible fraction AND small absolute count → KILL." 0.5% of attempts,
   absolute count 2, is textbook KILL. The auto-verdict inverted its own rule.

2. **Corpus can't exhibit the tail (fatal design flaw).** The base corpus is W4
   Opus survivors — tiny specs. Real BFS completions here: median 0.66s, p90
   0.70s, and only 2 of 102 exceed the cap. On specs this small BFS finds any
   violation essentially instantly, so a "BFS-slow broken tail" cannot exist by
   construction. LEWM's motivation was always the LARGE/hard specs (14, 141, 30…
   in the requirements doc's own data pull). This corpus is structurally the
   wrong instrument for the question.

3. **Operator contamination.** 2 of 4 operators produced ZERO usable broken
   specs: and_to_or → 150/150 TLC `error` (SANY-valid but TLC-uncheckable —
   the operator corrupts the temporal Spec/def structure, not the invariant),
   in_to_notin → 147/147 SANY reject (syntactically invalid mutation). The
   promised "large labeled-broken set" (target ≥300) never materialized; the
   effective sample is cup_to_cap + plus_to_minus = 103 mutants → 20 broken.

**Why KILL is nonetheless the right call, independent of this run's weakness:**
The scoping case against LEWM does not need this experiment to succeed — it
holds across everything measured:
- LEWM can only ship as option (b), post-hoc guided replay (Q1: no pluggable TLC
  state-ordering hook).
- By its own soundness carve-out it can ONLY help candidates that are actually
  broken — a correct candidate still requires the full exhaustive run. But at
  TLC-check time we don't know which candidates are broken.
- Broken-AND-BFS-slow candidates are empirically a handful everywhere we look:
  2 here, ~3 in the real repair/injected timeout data (lewm-sim-baseline), and
  61% of the requirements doc's real TLC timeouts are oracle/correct specs LEWM
  provably cannot touch.
- Free `-simulate` already covers part of even that handful (1/3 before), and
  where it doesn't (0/2 here) the residual is 2 cases — far below the cost of a
  permutation-invariant GNN state encoder + TLC per-state-trace instrumentation
  + the cross-spec transfer risk the requirements doc itself flags as the single
  biggest unmitigated risk.

Net: the addressable population is negligible against a very high build cost.
**Recommend parking LEWM.** The data, script, and this analysis stay in git; the
decision is reversible if a large-hard-spec broken corpus ever makes the tail
real. If Eric wants a genuine test rather than a park, the ONLY version worth
running is: broken mutants of the LARGE holdout specs (median ~97 LOC), not the
tiny W4 teacher specs — but that is a bigger build and the prior on payoff is low.

---

### (superseded) auto-generated verdict — KEEP

Retained for transparency; do not act on it. Original text: "The addressable
population is substantial: 2/20 (10.0%) confirmed-broken mutants are BFS-slow,
and TLC's own zero-training -simulate baseline fails to convert most of that
tail to a fast violation (0/2 converted). … KEEP LEWM, scoped narrowly to this
residual." — Rejected: 2/20 is n=2 on a corpus that cannot exhibit the tail
(see reasons 1–3 above).


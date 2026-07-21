# LEWM full-corpus KILL confirmation

2026-07-21. Full-corpus confirmation of the ratified KILL decision (docs/designs/2026-07-20-lewm-tlc-requirements.md, "Scoping result / disposition"), which was based on a 400-mutant-attempt sample over 150 of ~1839 eligible W4 Opus survivor specs (results/runs/lewm-scoping/). This run sweeps EVERY eligible survivor (not a sample), all 4 harness/mutation.py operators per spec where applicable, to check whether the addressable population (confirmed-broken AND BFS-slow) stays negligible at full scale.

(Coverage: 4778/4778 planned mutant-attempts across 1797 eligible survivors, full planned sweep completed.)

## Method

- Same corpus, same exclusions, same TLC invocation as results/runs/lewm-scoping/ (tools/lewm_scoping.py's load_survivors(), load_exclusions(), run_bfs_mutant/run_simulate_mutant, imported not forked). Eligible survivors deduped by seed_key (keep-last in shard-file append order, matching w4_exclusions.json's own dedup_overrides convention for correction rows).
- Each mutant: SANY-checked, then plain BFS TLC, 120s wall cap. Buckets identical to lewm-scoping: `invalid` (SANY reject), `vacuous` (BFS still passes), `error` (TLC crash unrelated to the invariant), `confirmed_broken` (BFS found a violation OR timed out).
- N = 4778 mutant-attempts across 1797 distinct base specs and 4 distinct mutation operators.

## Attempted / confirmed-broken / vacuous (all operators)

| bucket | n | fraction of N |
|---|---|---|
| attempted (N) | 4778 | 100% |
| invalid (SANY reject) | 1684 | 35.2% |
| vacuous (BFS pass) | 1008 | 21.1% |
| error (crash, not counted) | 1819 | 38.1% |
| **confirmed_broken** | **267** | **5.6%** |

### By mutation operator

| operator | attempted | invalid | vacuous | error | confirmed_broken |
|---|---|---|---|---|---|
| and_to_or | 1797 | 0 | 0 | 1797 | 0 |
| cup_to_cap | 1103 | 0 | 974 | 7 | 122 |
| in_to_notin | 1714 | 1684 | 5 | 7 | 18 |
| plus_to_minus | 164 | 0 | 29 | 8 | 127 |

Note (expected, per task design): `and_to_or` structurally corrupts the temporal Spec definition -> SANY-valid but TLC-uncheckable `error`; `in_to_notin` structurally hits quantifier bindings -> SANY reject. Both run anyway (reflects the real pipeline); the headline below is computed both including and excluding them.

## THE HEADLINE: BFS time-to-first-violation, computed two ways

### (a) All confirmed-broken mutants, regardless of operator

| stat | seconds |
|---|---|
| median (p50) | 0.64 |
| p90 | 0.66 |
| p95 | 0.69 |
| p99 | 0.74 |
| max | 0.78 |

4 confirmed-broken mutants had BFS itself time out at the 120s cap without ever finding the violation.

**Addressable population (a):** 4 / 267 (1.5% of confirmed-broken, 0.1% of all 4778 attempted).

### (b) Restricted to checkable operators only (cup_to_cap, plus_to_minus)

(1267 attempts, 249 confirmed-broken under this restriction)

| stat | seconds |
|---|---|
| median (p50) | 0.64 |
| p90 | 0.67 |
| p95 | 0.69 |
| p99 | 0.75 |
| max | 0.78 |

4 confirmed-broken mutants (checkable operators only) had BFS time out at the 120s cap.

**Addressable population (b):** 4 / 249 (1.6% of confirmed-broken under this restriction, 0.3% of 1267 checkable-operator attempts).

## Simulate head-to-head on the slow tail

Of the 4 confirmed-broken BFS-slow/timeout mutants (definition (a), all operators), 4 were run under `-simulate num=100000 -depth 100` seeds [0, 1, 2], 120s cap per seed.

- Converted to a fast violation under -simulate: 0/4 (0.0%).
- Did NOT convert: 4/4.

## VERDICT

**CONFIRMED**

KILL CONFIRMED at full-corpus scale. Addressable population (a, all operators): 4/267 (1.5% of confirmed-broken, 0.1% of all 4778 attempted). Restricted to checkable operators only (b): 4/249 (1.6%). Both readings stay negligible and absolute counts stay tiny, consistent with the 150-spec scoping sample (2/20, 0.5% of attempts). LEWM's entire addressable population (option-(b) post-hoc guided replay, per the design doc's Q1) remains ~zero at full scale. The ratified KILL stands.


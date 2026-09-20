# Tuned120B SANY diagnostic — 2026-09-05

No complete saved generation/loop run reaches 30/30 SANY coverage. Best is
28/30 (93.3%). The A/L union is 30/30, but combines configurations/seeds and
does not establish the requested single-configuration milestone. No production
lint or scoring changes were made. Main owns the compute pilot and full-scorer
repair probe.

## Audited baseline

Run names below expand under `results/runs/`. Counts are a snapshot of local
ledgers, not a declaration that active runs have finished. First attempt means
`greedy` for A and `c0r0` for L, after retry reconciliation.

| Run | Raw / dedup scored rows | SANY pass / scored rows | Pass / rows with SANY result | First attempt | Any-pass coverage | Missing specs |
|---|---:|---:|---:|---:|---:|---|
| gate2-w4dgm-120b-A | 990 / 990 | 290/990 (29.3%) | 290/990 (29.3%) | 12/30 (40.0%) | 28/30 (93.3%) | 142, 148 |
| open-w4dgm-120b-samesession | 960 / 960 | 281/960 (29.3%) | 281/959 (29.3%) | 14/30 (46.7%) | 28/30 (93.3%) | 106, 142 |
| loop-w4dgm-120b | 621 / 621 | 182/621 (29.3%) | 182/621 (29.3%) | 12/30 (40.0%) | 27/30 (90.0%) | 106, 142, 148 |
| loop-w4dgm-120b-seed2 | 1085 / 860 | 125/860 (14.5%) | 125/519 (24.1%) | 14/30 (46.7%) | 28/30 (93.3%) | 128, 148 |
| loop-w4dgm-120b-seed3, partial | 20 / 20 | 7/20 (35.0%) | 7/20 (35.0%) | 0/2 (0%) | 2/30 (6.7%) | Other 28 unobserved |

Seed2 has 225 duplicate rows and 341 unresolved API errors. Open-samesession
has one API error. API errors are not SANY failures; dropping them changes the
denominator and must be labeled. All six audited cohorts match
`harness.gate_check.gate_check` scored-row counts exactly. There were no malformed
lines or unavailable SANY-failure logs in this snapshot.

Framing B is corruption repair, not generation: 766 raw rows, seven corruption
control rows excluded, 759 scored rows, 652 SANY passes (85.9%), 106 failures,
one extraction failure. It covers 23/23 attempted specs; seven specs were not
attempted. Do not describe those seven as SANY failures or mix B into generation
coverage.

Loop row-0 generations versus later repair rounds: original loop 50/186 (26.9%)
versus 132/435 (30.3%); seed2 43/228 (18.9%) versus 82/632 (13.0%); partial seed3
5/16 (31.3%) versus 2/4 (50.0%). These denominators include API errors. Selection,
early stopping, and different prompts make these descriptive, not causal gains.

## Failure classes from saved SANY sections

Counts below are rows containing the diagnostic, not individual occurrences.
Classes overlap, and later errors can be hidden behind an initial parse or
missing-module failure. TLC log sections are excluded.

| Class | A | Open | Loop | Seed2 |
|---|---:|---:|---:|---:|
| SANY failures, denominator | 700 | 678 | 439 | 394 |
| Parse | 310 | 288 | 146 | 164 |
| Unknown named operator | 255 | 275 | 177 | 167 |
| Duplicate declaration/definition | 103 | 88 | 85 | 54 |
| Operator arity | 73 | 60 | 65 | 62 |
| Missing source module | 34 | 27 | 25 | 10 |
| Unresolved operator symbol, e.g. `-.`, `@@` | 30 | 46 | 40 | 24 |
| Precedence conflict | 44 | 30 | 11 | 27 |
| Level/temporal-action mixing | 6 | 4 | 14 | 5 |
| Unsupported expression | 4 | 6 | 0 | 4 |
| Undefined `@` | 2 | 2 | 2 | 1 |
| Other diagnostic | 0 | 1 | 0 | 2 |

For example, seed2 failures contain parse errors in 41.6%, unknown operators in
42.4%, arity errors in 15.7%, and duplicate diagnostics in 13.7%. These percentages
cannot be added or interpreted as independently recoverable mass. The script
emits exact message blocks, named-operator counts, example source-log paths,
per-spec classes, and all status/verdict counts for further inspection.

## Current frontier and recommendation

Seed2's frontier is **128 and 148**. Historically the full-run frontier includes
106 and 142 as well. Keep these distinctions when selecting pilot targets.

- **106:** A has 2/33 SANY passes; original loop 0/32; open 0/32; seed2 4/32.
  Original loop has 21 parse-failing and 11 unknown-operator rows. `FoldSeq`,
  `Permutations`, and `RemoveAll` recur. `FoldSeq` exists in the installed
  `SequencesExt.tla`; an unknown operator is not evidence that the harness
  failed to install the module. Imports and operator signatures must be checked.
- **142:** A 0/33, open 0/32, loop 0/32, seed2 1/3. Missing modules affect
  18 A, 14 open, and 16 original-loop rows; duplicate diagnostics affect only
  3, 4, and 12 respectively. This corrects the older duplicate-only emphasis
  in `docs/RALPH_STAIRCASE.md`. A greedy asks for `ReachableAlgs`; isolated
  replay again cannot resolve it, while correctly copying `Reachable`.
  Seed2 `c2r0` replays successfully without this dependency. No evidence here
  establishes a current dependency-copy pipeline bug.
- **128:** Seed2 0/32, including 15 parse, seven duplicate, six unknown-operator,
  four missing-module, four arity, and four unsupported-expression rows.
  Other configurations have passing candidates, but that does not close seed2.
- **148:** A 0/33, loop 0/32, seed2 0/32; open sample 31 is the sole pass among
  32 open candidates and passed isolated replay. Seed2 has 24 arity, 16 unknown,
  11 duplicate, and four parse rows. Undefined names vary (`Balance`,
  `BalanceRec`, `Chain`, `ledger`, etc.). This needs coherent model-generated
  operators, scope, and signatures; no demonstrated generic safe rewrite closes it.

Recommendation: evaluate the main pilot against one predeclared configuration,
report first-attempt and any-pass coverage separately, and prioritize seed2's
128/148 gap. Use the full-scorer probe to distinguish compile recovery from
behavioral recovery. Do not enable generic regex lint based on SANY alone.

## Local replay evidence and deterministic-fix boundary

Replays used the repository's `check_sany`, current Java/JAR/library path, and
the scorer's transitive, patch-aware corpus dependency copying in fresh temporary
directories. Candidate hashes were checked before replay. They did not invoke
TLC, TLAPS, generation, or alter saved candidates.

Representative original failures reproduced: A `2:1` and `2:6` parse errors;
`2:3` duplicate bound `p`; `2:4` unknown `Die`/`coord`; `2:15` unknown `broken`;
`55:2` and `55:13` temporal/action mixing; `128:31` missing `Automorphisms`;
`131:greedy` missing `MajorityVote`; `14:2` unsupported `[` expression.

Concrete warning against interpreting deterministic editing as safe repair:
A `2:30` changes from SANY fail to pass when existing lint drops the second
`Decide` definition. But source lines 68 and 131 implement different actions:
coordinator decision versus participant finalization. Deleting one loses intended
behavior. This is a reproducible compile recovery, **not a safe pipeline fix**.
Adding imports in the `131:greedy` example leaves its missing-module failure.

Additional controls: A `142:greedy` still fails on missing `ReachableAlgs`;
seed2 `142:c2r0` passes; open `148:31` passes. These support the observed frontier
without claiming proof of behavior. The full-scorer results under
`results/diagnostics/sany-repair-20260905-v2` are owned by main and were not
incorporated into this report.

The concrete accounting defect is in `tools/staircase.py`: its docstring promises
deduplication, but `scan()` iterates every row without deduplication or the API
retry replacement rule. It also mixes broad run populations and uses final
verdicts to infer rungs. This can inflate attempts and is unsuitable for these
cohort claims. The new diagnostic fixes its own accounting only; staircase and
production files remain untouched.

## Reproduction and snapshot identity

Run from the repository root; output is JSON on stdout:

```sh
python3 -B tools/sany_diagnostic.py
python3 -B tools/sany_diagnostic.py --replay 2
python3 -B tools/sany_diagnostic.py \
  --case gate2-w4dgm-120b-A:2:30 \
  --case gate2-w4dgm-120b-A:142:greedy \
  --case loop-w4dgm-120b-seed2:142:c2r0 \
  --case open-w4dgm-120b-samesession:148:31
```

Each ledger is read once. Dedup keys are `(run, str(spec), str(sample))`; keep
first except an API error yields to a later scored result. Content hashes are
not used to collapse distinct sampling attempts. Exact duplicate model output
at different sample IDs remains separate. The script follows gate terminology:
“scored” includes unresolved API errors, but reports them separately.

SHA-256 of ledger bytes used for the table:

| Run | SHA-256 |
|---|---|
| A | `2c8e91a69536f6363f4ce62f9225ea2ec344cfe1acc47bb9c3b4d296e6167c92` |
| Open | `070c73771ca55434de944ca2182c10220d8b2c9e471b4234faaa42a6b4c972c5` |
| Loop | `35ca7de417b405e555a19a61f0f0efe9e9fdefa02388ffd99aae453e106491ed` |
| Seed2 | `a8bcb4b491af1c8c94bac281512ad14ed5ac5a8aec6d4d01bef28cfed4673541` |
| Seed3 partial | `aca15fa7341275984ddeee01d320ee7103209664c0bda63304a56605db086b52` |
| B | `48e4817a3982bfd010b61edbe5cf5672699387c1a6a088ba0691263ea325ae6c` |

Limits: active ledgers may advance; the report does not freeze their files.
The run allowlist is names containing `w4dgm-120b`, with quarantine/smoke/aborted
runs excluded; it does not aggregate other tuned checkpoints. Replay uses current
local dependencies, not an archived environment. Classification is text-based,
retains an explicit other bucket, and does not prove root cause for every row.
Bounded replay is not an unbiased estimate of lint recovery. No production-safe
SANY pipeline repair or 100% per-configuration milestone is established.

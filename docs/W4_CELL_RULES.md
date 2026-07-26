# W4 per-cell rules

The cloud routine reads this file once per run (see `docs/CLOUD_ROUTINE_W4.md`).
It is the long tail of 51 waves of incident response; the scheduler prompt stays
short by pointing here instead of carrying it. Every rule below is
non-negotiable — each one exists because something went wrong without it.

## Hard floors, checked BEFORE append

- 40–90 non-comment LOC, 4–6 variables, ≥4 actions, <100k reachable states.
- Every spec written from scratch. No templating — a shingle audit quarantines
  near-duplicates.

## Natural language

- The NL scenario ends `SAFETY PROPERTY: <one sentence>` and must describe the
  FULL final action set. Actions added during repair go into the NL *before* the
  final verify.
- LIVENESS cells add `LIVENESS PROPERTY: <one sentence>` after the safety line.

## Module and config

- Module `W4O<key-without-dashes>`; the `.cfg` lists ONLY the substantive safety
  property as `INVARIANT` (never `TypeOK`).
- **CFG richness** — 32.4% of the corpus is the bare 3-line
  `INIT`/`NEXT`/`INVARIANT` cfg; stop adding to that pile. Parameterise the module
  with `CONSTANTS` instead of hardcoding set/bound literals, and bind them on a
  `CONSTANTS` line. Prefer `SPECIFICATION Spec` over the `INIT`/`NEXT` pair. Add a
  `CONSTRAINT` only when it is what actually holds the state count under the
  floor — never as decoration.
- **Comments** — 77% of the corpus has `comment_ratio` 0.0, which does not look
  like human TLA+. Carry 2–5 short comment lines explaining the mechanism and the
  invariant's intent. Comments do not count toward the non-comment LOC floor.

## Arm (from the shard file; lattice parity, NEVER reassign)

SAFETY-ONLY cells follow everything above unchanged. LIVENESS cells additionally:

- The spec defines a real eventuality (`<>` or `~>`) implementing the NL's
  liveness sentence, and `Spec` includes the `WF_`/`SF_` fairness that makes it
  true.
- The `.cfg` uses `SPECIFICATION Spec` and checks the eventuality on a `PROPERTY`
  line. The `INVARIANT` line stays the safety property, and `--invariant` still
  names the safety property.
- Verify with the extra flag `--require-liveness`.
- Prefer non-quantified named `WF_`/`SF_` conjuncts. Quantified fairness
  (`\A c \in Cars : WF_...`) has made the FIX-5 stutter-stripper return
  `inconclusive:error`.
- The FIX-5 gate re-runs TLC with fairness stripped and REJECTS
  `liveness_stutter_trivial` unless the property FAILS there. An Init-true or
  stutter-insensitive eventuality cannot pass. Do not game this with
  `<>TRUE`-shaped properties — write progress the mechanism actually guarantees
  ("every admitted request is eventually serviced", "the token eventually returns
  to the ring").
- The liveness arm is the scarce half of this corpus. A liveness cell you give up
  on costs more than a safety cell you add, so spend the full repair budget before
  recording a non-survivor. Never downgrade a LIVENESS cell to SAFETY-ONLY to make
  it pass — a failed liveness cell is an honest non-survivor.

## Verify

```
python3 -m harness.w4_verify_cell --nl .. --spec .. --cfg .. --invariant .. \
    --workdir /tmp/... [--require-liveness]
```

Max 4 repair attempts. If the budget is exhausted, record an honest non-survivor:
an honest 24/25 beats a gamed 25/25.

## Ledgers

Both are append-only. Never edit or strip a row.

- `results/runs/w4-opus-shard<S>/w2_survivors.jsonl` — one survivor row per cell.
  Row = the verifier JSON merged with
  `{"cell","seed_key","nl","teacher":"claude-opus","tier":"complex"}`.
  The FULL dashed key goes in both `cell` and `seed_key` (`w4opus::<key>`).
- `results/runs/w4-opus-shard<S>/w4_attempts.jsonl` — one row per cell attempted,
  `{"cell","arm","survived","rejection_reason","attempts"}`. Non-survivors go here
  and ONLY here; the reject histogram is the only telemetry we have on what the
  gates actually catch.

Assert before every append: `module == "W4O" + key-without-dashes`; key matches
`d\d+-m\d+-p\d+-t\d+`; and for LIVENESS cells, the verifier JSON carries non-null
`liveness_property` and `stutter_check`.

Corrections are NEW rows flagged `"keep_last"` — that exact spelling. `keep-last`
and `keep` both exist in older rows and the audit reads neither.

## Invariant quality and diversity

- One substantive claim. No conjuncts guaranteed by typing, or by monotonic
  bookkeeping no action can violate.
- Prefer implication / subset / coherence / staleness / log-contiguity shapes.
  Avoid `Cardinality <= 1`, `applied + Len = admitted`, ghost `badActions`, bare
  `count <= 1`, pairwise slot-uniqueness, and counter-vs-cardinality where an
  honest alternative exists. A discouraged shape is fine when it IS the literal
  property — disclose that in the commit body.
- **Family drift (advisory).** `mutex_locks` is ~35% of the corpus against ~1% for
  `replication_storage`. The lattice is fixed, but the skew is partly vocabulary:
  when the cell's MECHANISM is lock-flavored (optimistic locking, hierarchical
  locks, leases, CAS, token ring) but its PROPERTY is NOT mutual exclusion, write
  the NL in the vocabulary of the actual property — conservation, staleness,
  capacity, authorization — instead of reaching for lock/mutex language.

## Integrity

- Never read `harness/mutation.py`, `harness/w2_loop.py`, or any harness internals
  beyond `w4_verify_cell`'s JSON output.
- Never run gate-mapping probes of any kind, including against prior shards' specs
  or synthetic specs. The ban is on the behavior, not the substrate.
- Direct SANY/TLC (`tools/tla2tools.jar`) on your OWN current modules in `/tmp` is
  allowed, for counterexample diagnosis.
- `no_kill` / `no_site` are honest outcomes. Report them as-is.

## Incidents → `results/analysis/w4_exclusions.json`

| Incident | Action |
| --- | --- |
| Near-dup pair | loser's key into `excluded_seed_keys` |
| Keep-last correction | key into `dedup_overrides` with a short reason |
| Malformed key | `excluded_seed_keys` + note |
| LIVENESS cell appended without `liveness_property` | `excluded_seed_keys` + note (the arm split must stay honest) |
| Internals read or gate probe you committed | ALL affected seed_keys into `mutation_evidence_untrusted` + note, disclosed in the commit body |

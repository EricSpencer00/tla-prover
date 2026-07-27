# W4 stutter-vacuity re-check — 133 `inconclusive:error` rows (2026-07-26)

## What was wrong

`strip_fairness` (harness/w2_loop.py) implemented the FIX 5 stutter-vacuity
check by **deleting** each `WF_`/`SF_` application from the module text. That
breaks the standard multi-process fairness idiom:

```tla
Spec == Init /\ [][Next]_vars
        /\ \A c \in Controllers : WF_vars(Step(c))
```

Deleting the `WF_` term leaves the binder dangling — `... /\ \A c \in
Controllers :` — and where fairness was its own definition (`Fairness == \A c
\in C : WF_v(Step(c))`) it emptied the body outright. **43 of the 45 affected
specs had an empty or truncated definition body after stripping.**

Both are SANY parse errors, so `check_tlc` returned `error` (not `fail_*` —
see `harness/runner.py:classify_tlc`), the gate recorded
`stutter_check="inconclusive:error"`, and the row was **accepted under the
no_kill philosophy with the vacuity check never actually run**.

The systemic cost was larger than 45 rows: the bug exempted precisely the
parameterized-concurrency specs — the ones using `\A p \in Procs :
WF_vars(Step(p))` — from the liveness vacuity gate.

## Blast radius: contained

A parse error cannot masquerade as a pass. `classify_tlc` only returns
`fail_invariant` / `fail_deadlock` / `fail_liveness` on specific TLC output
strings, and the gate's non-trivial condition is `st_status.startswith("fail")`.
So the 250 rows already recorded `nontrivial` were verified correctly. Only the
45 `inconclusive:error` rows were unverified.

## The fix

`strip_fairness` now **substitutes `TRUE`** for each fairness application
instead of deleting it. `\A p \in Procs : TRUE` reduces to `TRUE` and `/\ TRUE`
is the identity conjunct, so the fairness-free closure is semantically
identical while every binder and conjunct stays well-formed.

Regression tests added in `harness/test_w2_loop.py`:
`test_strip_fairness_quantified_keeps_module_parseable`,
`test_strip_fairness_never_empties_a_definition_body`,
`test_strip_fairness_nested_quantifiers`.

## Scale: the cloud routine ran with the bug live

The bug was found at local shard 178, but the W4 cloud routine had continued
to shard 196 in the meantime. Measured on `main` at commit 3646b6b6 (4910
effective rows, 517 liveness):

| liveness rows | 519 |
|---|---|
| `nontrivial` (verified) | 386 |
| `inconclusive:error` (**unverified**) | **133** |

That is 45 rows from shards ≤178 plus **88 more generated after**, i.e. ~39%
of every liveness row the routine produced post-178. For a period the reported
liveness count (517, against a floor of 500) rested on 133 rows whose vacuity
gate had never actually run.

## Re-check result: all 133 clear, 0 rows dropped

Every one of the 133 was re-run through real TLC on the corrected fairness-free
closure (90s timeout; per-row results in `w4_stutter_recheck_2026-07-26.json`):

| verdict | n |
|---|---|
| `nontrivial` (property FAILS without fairness — correct) | **133** |
| `STUTTER_TRIVIAL` (would have been dropped) | 0 |
| still inconclusive | 0 |

All 133 returned TLC status `fail_liveness`. Fairness applications per spec:
1×43, 2×39, 3×24, 4×16, 5×9, 6×2 — the multi-application cases are exactly the
quantified/multi-conjunct forms the old stripper mangled.

**Corpus impact: none negative, and the floor genuinely holds.** No survivor
count changes. The liveness arm stays at 517, but all 517 are now actually
vacuity-verified rather than 386 verified + 133 assumed. Stop floors as
reported by `w4_audit.py`: 4910/5000 total, 517/500 liveness.

## Follow-up

The 133 rows' stored `stutter_check` field still reads `inconclusive:error` in
the shard files. It was left as-written rather than rewritten in place — the
shard outputs are the immutable record of what the loop actually observed, and
this document plus the JSON is the correction. Any consumer computing liveness
quality should treat the 133 keys listed in the JSON as `nontrivial`.

Because the fix landed after shard 196, no future wave can reproduce this:
`strip_fairness` now substitutes rather than deletes, so a quantified-fairness
spec yields a parseable closure and the gate runs for real.

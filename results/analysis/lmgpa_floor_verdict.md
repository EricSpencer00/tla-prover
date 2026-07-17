# lmgpa 0-model baseline: honest floor

**Verdict: 0/119.** All 119 "pass" rows in `results/runs/lmgpa-baseline-tlapm/rows.jsonl` are vacuous
w.r.t. the benchmark's actual theorem. tlapm reports "pass" whenever a module has zero *failed*
obligations, including zero total obligations — which is exactly what a bare `THEOREM Foo == ...`
with no `PROOF`/`BY` produces: tlapm never attempts the goal, so it can't fail it.

## Evidence

1. **116 zero-obligation modules** (e.g. `10_lockserv`, `distributed_ind_inv`): direct tlapm run
   reproduces the ledger exactly —
   `[INFO]: All 0 obligation proved.` / exit 0 — for a module whose only content is
   `THEOREM Inductiveness == IndAuto /\ Next => IndAuto'` with no proof body. tlapm parses the
   statement, finds no `PROOF`, and emits zero obligations rather than one big unproved goal.
   Same for `aimeII_2001_p3.tla` (math/minif2f): `All 0 obligation proved.`, main theorem has no proof.

2. **3 modules with 18 total obligations** (`induction_ineq_nsqlefactn`, `mathd_numbertheory_457`,
   `exercise_3_10`, 6/6 each): inspected source — in all three, the 6 proved obligations belong
   entirely to a shared **helper lemma** (`FactorialDefConclusion`, a generic factorial-induction
   fact, or its `proofnet` analogue) that ships pre-proved in the module. The **actual benchmark
   theorem** (`induction_ineq_nsqlefactn`, `mathd_numbertheory_457`, `exercise_3_10`) has **no
   `PROOF`/`BY`** and contributes 0 obligations, same as the other 116. So these 3 are not
   partial credit toward the target theorem either — the model-relevant floor here is also 0/3.

Net: 0/119 target theorems are tlapm-certified without a model. The "18 obligations proved" only
certifies scaffolding lemmas the benchmark authors already proved, never the theorem being scored.

## Parsing gap

`harness/runner.py:281-284` (`check_tlapm`):
```python
m = re.search(r"All (\d+) obligations? proved", out)
if m:
    n = int(m.group(1))
    return "pass", n, n, out, dt
```
This treats `All 0 obligation proved` identically to `All N obligations proved` for N>0 — both
return `status="pass"`. It has no way to distinguish "everything proved" from "nothing was
asked." There is also no check that the specific theorem named in the manifest
(`entry["theorem_name"]`) is the one covered by the counted obligations — `check_tlapm` counts
*all* obligations in the file, so a module with unrelated pre-proved helper lemmas (as in the 3
above) inflates `proved`/`total` even when the target theorem itself is untouched.

## Fix needed (not applied)

In `harness/lmgpa_bench.py` / `harness/runner.py::check_tlapm`, per-theorem pass criterion should be:
"tlapm certifies the *named* `theorem_name` specifically, via a proof, with zero failed and zero
omitted obligations under that theorem's proof tree" — not a whole-file obligation tally. Concretely:
- Reject `total == 0` as `pass`; classify it separately (e.g. `"no_proof"`), not `"pass"`.
- Scope obligation-counting to obligations that occur under the target theorem's own `PROOF` (tlapm's
  per-obligation output includes source line ranges — filter to the target theorem's line span from
  `theorem_name`'s declaration to the next top-level `THEOREM`/`----`), not module-wide.
- Only `status="pass"` when total > 0 and proved == total *for that scoped range*.

# TLAPS wiring — proof_module population (Amendment 1)

Scope: `harness/runner.py` gained a `tlaps` stage (`check_tlapm`, moved from
`harness/proof_tools.py` to avoid a circular import — `proof_tools.py` now just
re-exports it for the standalone tool-smoke CLI). Applied to the 9 specs classified
`proof_module` in `corpus/configs/populations.json`. Population classification for the
remaining specs (state_machine/mc_wrapper/library) is not yet complete — tracked as a
prerequisite for the full Gate 0 sweep.

Reproduce:
`python3 -m harness run --run-id tlaps-proof-modules --specs 67,112,118,119,131,137,139,142,182 --stages sany,tlc,tlaps --timeout 120 --jobs 4 --extra-cfg-dir corpus/configs/drafts`

## Harness bug found and fixed while wiring this

`check_tlapm`'s output parser only recognized `"All N obligations proved"` and
`"N/M obligations proved"`. Real tlapm output on a *partially*-failing proof reads
`"N/M obligations failed"` — the parser fell through to `error, 0/0`, which would have
under-reported spec 112 as a total failure instead of 642/654 proved. Fixed by adding
a third regex branch (`failed` → `proved = total - failed`, status `partial`).

## Results (SANY ∧ TLAPS, oracle method = canonical corpus proof scripts verbatim)

| spec | module | tlaps | obligations |
|------|--------|-------|-------------|
| 67  | EWD840_proof          | **pass**    | 65/65   |
| 118 | AddTwo                | **pass**    | 18/18   |
| 119 | FindHighest           | **pass**    | 45/45   |
| 131 | MajorityProof         | **pass**    | 97/97   |
| 137 | ParReachProofs        | **pass**    | 52/52   |
| 139 | ReachabilityProofs    | **pass**    | 64/64   |
| 142 | ReachableProofs       | **pass**    | 73/73   |
| 182 | sums_even             | **pass**    | 21/21   |
| 112 | LamportMutex_proofs   | partial | 642/654 |

8/9 proof modules fully close under Amendment 1's criterion (SANY ∧ all TLAPS obligations
proved). This is the *oracle* method — the corpus's own reference proof scripts checked
verbatim through tlapm, not model-generated proofs; it establishes the harness correctly
recognizes valid TLAPS proofs (Stage 0's job), not a G2 generalization result.

## Corpus finding: spec 112 (LamportMutex_proofs), 12/654 obligations fail

`tlapm` reports 12 failing obligations in `LamportMutex_proofs.tla`, including at least
one around line 374 (a `network'` clock-ordering step in the mutual-exclusion proof) and
a `TypeOK'` induction step near line 811. Not yet root-caused — needs a step-by-step
`tlapm --toolbox` pass to isolate which of the 12 are missing hypotheses vs. genuine gaps
in the corpus's proof. Routed per Amendment 1 ("corpus defects must be repaired from
upstream sources") — left as a documented partial pending that investigation, denominator
unchanged.

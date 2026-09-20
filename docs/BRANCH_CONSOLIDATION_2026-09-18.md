# Branch consolidation audit, 2026-09-18

This audit records the quality boundary used to consolidate the AI4FM remote
branches into `main`. A branch name is not evidence that its full tree belongs
on the release line. Generated snapshots, incomplete dependency closures, and
unreproducible ledgers stay outside `main` even when their history remains
available on the source branch.

## Promoted

| Source | Promoted artifact | Verification |
|---|---|---|
| `origin/board/192` | W4 floor-marker implementation and regression tests | Included in the full harness run |
| `origin/board/193` | TLAKit notebook, non-interactive Polaris/Sophia probes, tests | Notebook executed; live SANY pass; adapter tests pass |
| integration branch | Public evidence hub and GitHub Pages workflow | Desktop/mobile visual review; live browser SANY pass; JavaScript syntax check |
| `origin/fix/strip-fairness-quantified` | No action required | Already an ancestor of `main` |

## Rejected or deferred

| Source | Decision | Reason |
|---|---|---|
| `origin/board/49`, `origin/board/52` | Deferred | Both point to the same E2.c ledger history. A trial promotion failed because `tools/e2c_ledger.py --check` requires run directories absent from `main`. Publishing the table without its inputs would break the repository's reproducibility contract. |
| `origin/worktree-agent-a88b5a8eaaf7bf055` | Rejected | Its only source change modifies `tools/otp_nag.sh`, a file intentionally removed from current `main`; its result rows already overlap the corpus history. |
| `origin/w2-rft-pipeline-20260711` | Rejected | 307 commits behind `main`, five commits unique, and superseded by the signed-off Stage-2/W4 history. |
| bulk of `origin/board/193` | Deferred | The branch contains roughly 25,000 changed files and 17 million inserted lines, mostly staged experiment artifacts and board snapshots. Only independently verifiable deliverables were promoted. |

## Release verification

```text
401 passed, 1 skipped
```

The browser workbench also returned a mechanical `SANY PASS` against TLAKit's
isolated public runner. That verifies the webpage's toolchain path only. It does
not alter the protected prover result, which remains 0/119.

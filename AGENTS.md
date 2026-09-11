# prove-TLA local agent directive

- Apply [the quality pillars](docs/PROVER-QUALITY.md) before implementation acceptance, model promotion, remote experiment preparation and completion claims. They supplement the frozen goal; historical experiment notes cannot weaken them.
- Keep the native objective active: 100% SANY pass, then 100% applicable TLC, then non-vacuous intended behavior on unseen specs.
- Do not downgrade or narrow the objective. Preserve append-only evidence and explicit unknown/infra failure accounting.
- Run a bounded local loop on each branch: reproduce quickly, patch minimally, run targeted verification, then advance only with measured gain.
- For orchestration/monitoring, use `gpt-5.3-codex-spark` as the default verification loop target (including escalations previously assigned to Luna).
- Preserve all checkpoints, manifests, and summaries; continue from frozen baselines unless a causal bug is reproduced and fixed.
- Never treat infra crashes or parse issues as model success; keep these excluded from score claims.

## Goal board accuracy

- `docs/PROVER-BOARD.md` is the only current execution state. Automation prompts, memory, archived boards and old handoffs are not alternative status sources.
- Read/publish/check with `python3 tools/prover_board.py`; use a temporary draft and the SHA returned by read. Reconcile concurrent changes instead of overwriting. Never prepend handoffs or directly append competing current sections.
- Revalidate live ownership and actual receipts before acting. Publish actual UTC observations and every meaningful transition before the next side effect or final handoff. Failed checks mean unverified, never an assumed active job or empty queue.
- Update task status and evidence together. Reopen Done when its required evidence is invalidated. Local smoke tests must exercise the exact complete stage; naming a new objective does not prove the implementation changed it.
- Keep memory as a concise pointer to the board. Preserve historical evidence in `results/board-history/`; it is not executable direction. Unchanged external waits need no repeated narrative or tests.
- Before every future `qsub`, claim the stable experiment and payload identity with `tools/prover_submit_guard.py` and preserve its receipt. An `existing` claim or a collision stops submission; bypassing the guard is not an authorized submission path.

## Frequent commits

- Commit each coherent, verified implementation or experiment-preparation change as it completes, and checkpoint completed work before a handoff or remote experiment. Do not accumulate several finished changes across loop runs.
- Stage explicit files belonging to that change, include the relevant tests and small reproducibility records, and preserve unrelated edits. Coordinate Git index ownership with any other active worker.
- Keep secrets, model checkpoints, locks, temporary drafts and bulky generated outputs out of commits. Preserve large artifacts at their recorded locations and commit small manifests or receipts when needed.
- Record what changed and the verification in the commit message. A commit does not establish model improvement or gate completion; retain the actual measured result and unknowns.
- Do not make empty, unchanged-poll or timestamp-only commits. Commit locally; push only when requested.

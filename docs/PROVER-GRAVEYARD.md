# Failed approaches and reopening conditions

This is a record of lessons, not a second execution board. Current hypotheses,
ownership, attempt counts, active diagnosis time and next actions belong on
`PROVER-BOARD.md`. Preserve original receipts, including incorrect claims, and
link corrections. Retiring an approach does not retire the goal.

## 2026-09-11 — Direct paired generation v1: Triton inherited Polaris nvc

The first checkpoint-faithful paired run restored the model and wrote two ordinary row-47 records, but the first grammar-constrained candidate failed. XGrammar's Triton mask kernel inherited `CC=nvc`; its launcher compiler command includes GCC-specific `-Wno-psabi`, which Polaris nvc rejects. Do not retry this payload unchanged or remove the flag blindly. The launcher now pins GCC and includes a real mask-kernel smoke before the 8B model loads; a new authorized GPU run must verify that boundary before the paired contract is claimed.

## Diagnosis checkpoint

Before a new experiment, record the failure signature, hypothesis, cheapest
discriminator, expected result that would change the decision, and bounded
resources on the board. Check this record for the same failure first.

After two unsuccessful corrective attempts or 20 minutes of active diagnosis
without new discriminating evidence, stop the retry sequence. Time spent waiting
for a scheduler, authentication or user reply is external waiting, not active
diagnosis. Renaming jobs or crossing heartbeat boundaries does not reset counters.

At that checkpoint:

1. Inspect the earliest failing boundary and actual artifacts. Separate launcher,
   environment, data, checker and model failures; do not infer one from another.
2. Write at least two materially different explanations and choose the cheapest
   test that separates them. Prefer correcting an existing interface to adding code.
3. If local diagnosis is stuck, escalate one bounded expert diagnosis with exact
   evidence and a requested decision, using the existing owner or internal agents
   under the routing policy. Do not create more user-facing tasks.
4. Retire the unsupported approach or continue only with the new evidence and
   next discriminator recorded. Work on useful independent in-scope tasks during
   a genuine external wait. Respect rejected actions and approved resource bounds.

A negative model result triggers a plan review immediately. Compare matched
parent/child outcomes and preserved baselines. A flat or worse result cannot be
promoted; a retry needs a causal intervention, not just more training or sampling.
An inconclusive measurement requires fixing the measurement before interpreting it.

## Recorded lessons

### Wrong tokenizer/model selection

- Evidence: `results/runs/syntax-structured-polaris-20260911/job-7605175/tokenizer-mismatch-diagnosis.json`.
- Lesson: a launcher selecting Qwen cannot evaluate the frozen Llama checkpoint.
- Retired: unchanged mismatched launcher or scores without actual restore evidence.
- Reopen only after model/tokenizer identity and checkpoint compatibility are
  verified through the exact stage. This is an interface repair, not model progress.

### Training memory failure

- Evidence: `results/runs/syntax-structured-polaris-20260911/job-7605510/terminal-receipt.json`.
- Lesson: CUDA OOM needs a measured memory intervention; scheduler GPU accounting
  alone does not demonstrate contention or lack of GPU assignment.
- Retired: rerunning the unchanged memory configuration.
- Reopen only with a justified memory change and bounded actual training check.

### Summary crash mistaken for missing training artifacts

- Evidence: `results/runs/syntax-structured-polaris-20260911/job-7605656/artifact-recovery-correction.json`.
- Lesson: the run saved a checkpoint and evaluation outputs before summary failure.
- Retired: retraining solely to replace a missing summary without an artifact census.
- Reopen training only for a distinct learning hypothesis; recover existing results
  first and retain unknown summary-only metrics as unknown.

### Hand-written patches mistaken for model outcomes

- Evidence: `results/runs/syntax-structured-polaris-20260911/job-7605656/patch-only-protected-sany-eval-v2/summary.json`.
- Lesson: manually deleting an expression or inserting an incomplete conjunction
  produces negative controls, not evidence that a model or tokenizer failed.
- Retired: treating repeated fixture edits as model experiments or gate progress.
- Reopen a model claim only with actual generation, prompt, source and checkpoint
  provenance, scored under the frozen contract. Preserve fixtures as controls.

### PBS environment not reaching the launcher

- Evidence: `results/runs/syntax-structured-polaris-20260911/job-7605656/checkpoint-preflight-job-7606064-terminal.json`.
- Lesson: the launcher exited before the runner because its stage variable was absent.
- Retired: unchanged submission relying on ambient submit-shell variables.
- Reopen only after stage resolution is explicit and checked in the staged launch
  path. No model conclusion follows from this launcher failure.

### Polaris grammar dependency absent from the approved runtime

- Evidence: `results/runs/syntax-structured-polaris-20260911/job-7605656/checkpoint-preflight-job-7607519-terminal.json` and `checkpoint-preflight-xgrammar-inventory.json`.
- Lesson: package absence is an environment-closure defect, not proof that provisioning is unavailable. The v2 job loaded base weights and restored the checkpoint before the xgrammar import failed.
- Retired: unchanged v2 preflight submission and treating the missing import as an external wait without attempting an isolated closure.
- Reopen only with a hash-pinned isolated CPython 3.12 x86_64 dependency closure that passes CPU-only import and grammar parsing before any GPU allocation. A failure during provision must retain its exact package, resolver, and platform evidence.

## Adding or reopening an entry

Record: signature, attempted intervention, immutable evidence path, observed result,
scope of the conclusion, why this branch stops, and the specific new evidence
needed to reopen it. Use short entries; do not copy logs or accumulated handoffs.
Commit substantive lessons with their coherent change. Timestamp refreshes and
unchanged polls do not merit commits. Keep acceptance gates and the last verified
baseline intact while searching for a better plan.

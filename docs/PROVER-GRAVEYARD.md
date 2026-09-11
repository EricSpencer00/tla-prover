# Failed approaches and reopening conditions

This is a record of lessons, not a second execution board. Current hypotheses,
ownership, attempt counts, active diagnosis time and next actions belong on
`PROVER-BOARD.md`. Preserve original receipts, including incorrect claims, and
link corrections. Retiring an approach does not retire the goal.

## 2026-09-11 — Direct paired generation v1: Triton inherited Polaris nvc

The first checkpoint-faithful paired run restored the model and wrote two ordinary row-47 records, but the first grammar-constrained candidate failed. XGrammar's Triton mask kernel inherited `CC=nvc`; its launcher compiler command includes GCC-specific `-Wno-psabi`, which Polaris nvc rejects. Do not retry this payload unchanged or remove the flag blindly. The launcher now pins GCC and includes a real mask-kernel smoke before the 8B model loads; a new authorized GPU run must verify that boundary before the paired contract is claimed.

## Diagnosis checkpoint

### Structural grammar v0: closed 2026-09-11 with parser evidence

Corrected GCC run 7608598 finished all eight checkpoint-restored candidates.
Actual controlled SANY measured 0/4 ordinary and 0/4 grammar; both arms emitted
identical text for each protected row. Row 47 omits a conjunction in Init, and
row 107 omits conjunctions in NextBank. v0 explicitly permits arbitrary line
content, so it accepts both parser-rejected modules. Repeating unchanged v0
decoding is retired. The existing expression grammar v1 accepts both reference
controls and rejects both failures under local XGrammar 0.2.3. This is a causal
discriminator, not a model gain or proof of full valid-syntax coverage. Reopening
requires a syntax constraint that excludes the error class without false-rejecting
required valid constructs, exact runtime tests, and controlled generated results.
Evidence: `results/runs/syntax-structured-polaris-20260911/job-7605656/direct-checkpoint-paired-generation-job-7608598-diagnosis.json`.

### Parallel prompt preflight did not attest actual model tensors

Post-run replay of the exact tokenizer used in 7608598 found 402/458 actual
input tokens against frozen 401/457: default tokenization added a second BOS.
The separate preflight used `add_special_tokens=False` and therefore passed.
The raw SANY 0/4 per arm remains a valid diagnostic, but the earlier claim that
the generation honored frozen input tokens is withdrawn. `frozen_inputs` now
disables special-token addition and compares the actual generation tensor with
the packet before every candidate. Both exact-runtime CPU replays match after
this correction; no new GPU comparison is implied. Never use a parallel
preflight encoding as evidence for unchecked generation tensors.

### Board persistence correction, 2026-09-11

The assistant reported submission and completion of 7608598 in chat but failed
to publish them, leaving board250 at an already-resolved upload approval wait.
This was a missed workflow step, not a publisher malfunction or missing user
permission. Revisions 251 onward reconcile retrieved raw receipts and scoring.
Persist each transition before the next side effect; verify the published state
matches the final handoff. Never infer lack of authorization from stale board prose.

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

### Expression grammar v1: precedence gaps and mask cost

- Run7608834 used corrected actual401/457-token prompts and the frozen checkpoint.
  Six of eight candidates were saved: SANY rejected all six, with four correct
  positive/negative controls. Two row107 grammar candidates remain unknown.
- On row47 both arms produced the same conjunction/disjunction precedence
  conflict. v1 explicitly flattens precedence; accepting84/84 valid reference
  modules did not mean it enforces every syntax rule.
- Row107 ordinary output repeated to the1024-token cap. A90-second CPU replay
  compiled the grammar in4.1s but measured individual mask steps of1.5-3.0s;
  this cost exists without loading or running model weights.
- Retire unchanged v1 decoding and larger token-budget retries. Reopen only
  with a measured syntax-coverage/performance correction, or choose a distinct
  parser-aware representation that preserves the intended behavior. Do not
  call renderer/handwritten repairs learned-model successes.
- Requested PBS limit was15min; accounting reached16:42 before termination
  with exit-29. qdel issued after live16:31 observation returned job-finished.
  Future launcher source adds an inner840s timeout plus10s kill grace.
- Evidence: `results/runs/syntax-structured-polaris-20260911/job-7605656/expression-grammar-v4-job-7608834-terminal.json`
  and `expression-grammar-v4-cpu-mask-profile.json` beside it.

### Boolean-chain grammar simplifications: retired on CPU

- `precedence-probe-20260911-v3` scored all104 items with real SANY:14
  hand-written syntax controls,84 frozen training references,6 saved model
  outputs. Both variants still admit all4 row47 failed outputs. The recursive
  variant preserves84/84 references; the restricted-list variant loses2/84
  plus a valid nested-list control. Neither justifies GPU evaluation.
- A homogeneous infix chain is insufficient while quantified expressions and
  list bodies can re-enter permissive expression rules. Restricting recursive
  lists also loses valid syntax. Do not promote a variant just because it rejects
  small inline counterexamples.
- Three fixture expectations were corrected to match actual SANY. A bullet-list
  tail may contain an infix operator; mixed symbols alone do not prove a parse
  error. v1/v2 source snapshots, rows and failed-control summaries are preserved.
  Final controls pass without changing any checker or frozen reference/output.
- TLA+ uses partial operator precedence and layout-sensitive lists; see the
  [primary parsing explanation](https://lamport.azurewebsites.net/tla/tutorial/parsing.html).
  Reopen only with measured valid coverage AND rejection of actual errors,
  followed by bounded mask profiling. An explicit expression tree is a distinct
  representation hypothesis, not a complete-module solution or model gain.
- Evidence directory: `results/runs/syntax-structured-polaris-20260911/job-7605656/`.

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

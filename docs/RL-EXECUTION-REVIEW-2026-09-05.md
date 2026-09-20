# RL execution review, 2026-09-05

The previous turn delivered an optimizer unit test on a four-logit synthetic
policy. It did not complete the requested language-model RL experiment. Its
parameter delta and successful reload are mechanics evidence only.

## Evidence for the delays

- PLAN Amendment 16 records generation/repair task mismatch and a training loss
  reduction without a Gate-2 improvement. It also records that two of three
  measurement attempts were disrupted by infrastructure/configuration defects.
- PLAN Amendment 17 records repair training improving greedy performance from
  8/23 to 9/23 while reducing pass@4 from 17/23 to 9/23. That was a failed
  diversity/capability experiment, despite lower training loss.
- The August GRPO design remains proposed. The historical fullspec trainer in
  ChatTLA still enables `include_topics=True`; the design documents the historical
  holdout contamination. It cannot be used unchanged as a valid new experiment.
- The September 5 SANY diagnostic records 12/30 first-attempt SANY success in
  `gate2-w4dgm-120b-A`, versus 28/30 any-success coverage across 33 attempts per
  spec. Search coverage and single-attempt model capability are different.
- The current queued Sophia job 178956 serves evaluation. It performs no policy
  updates. Polaris BatchMode authentication failed again during this review.
- A syntax/model-checking model does not by itself establish TLAPS proving
  ability. The program has a separate proof-obligation objective and benchmark.

These observations support a process diagnosis: too few complete, trustworthy
training-to-evaluation cycles, combined with failed training hypotheses. They do
not establish that a useful prover model is impossible, or that a larger model
will resolve the problem.

## Corrections during this continuation

The small `tools/verifier_grpo.py` reference primitive now excludes unknown TLC
results and proof-module rows, rejects mixed prompt groups, places advantages on
the policy device, saves optimizer/reference state, and refuses checkpoint
overwrite. Its squared log-probability regularizer is explicitly not called KL.
Nine tests pass in the cached-model PyTorch environment. This primitive still
requires a trusted current-policy rollout producer; numeric spec exclusion is
not a substitute for near-duplicate decontamination.

The immediate experiment is a bounded online language-model curriculum with
actual sampled tokens and actual verifier outcomes. Any scaffolded repair result
must be reported with its scaffold and training population, and cannot be used
as a full-spec generation or held-out proving result. A successful optimizer
update alone does not justify a 120B scaling run.

## Executed local language-model experiment

Run `results/runs/online-rl-qwen-syntax-20260905-122859` trained the final
transformer layer of cached Qwen2.5-0.5B-Instruct on one-token source completion
of `THEN` in AdaptiveK from the decontaminated v3 training corpus. The source
hash matches its manifest; fresh maximum holdout Jaccard is 0.006316, below the
existing 0.65 cutoff. No holdout prompts were trained on.

Four fresh groups of 16 full-vocabulary samples produced three actual AdamW
updates; one group had zero reward variance and was skipped. The fifth group
was evaluation-only. SANY counts were 13, 15, 16, 15, 16 out of 16; probability
of the keyword increased from 0.892076 to 0.998594 on this same training prompt.
All 75 parse-passing candidates also passed TLC with no reported vacuity flags.
Reward was SANY-only partial credit, not a semantic-audited terminal pass reward.
No held-out/generalization result follows from this one-source experiment.

The run took 74.58 seconds on MPS, updated 14,912,384 parameters (change norm
0.171967), and saved 178,973,247 bytes of trainable weights and optimizer state.
Zeroing and restoring the trainable parameters reproduced logits exactly.
Earlier instruction-prompt attempts `122708` and `122816` produced zero updates;
their evidence remains present. Low entropy/repeated keywords on the successful
single-token task represent task saturation; full-spec diversity requirements
are not validated by this curriculum.

Reproduction (creates a fresh run directory):

```sh
tools/smoke/e2e/.venv/bin/python tools/online_rl_pilot.py --steps 4 --group-size 16
```

## Polaris replication

Interactive authentication succeeded after the user supplied the login code.
No credential is written to project files. Live queue inspection confirmed
debug permits 1–2 nodes and at most one hour; no other Polaris user jobs were
present before submission. Job **7593959** was submitted with EVITA, one Polaris
node, 15-minute allocation and a 720-second outer process deadline. It runs the
same cached Qwen checkpoint using one A100; this is a small GPU replication,
not 120B training. Staged files and outputs are isolated at
`/grand/EVITA/eric-spencer/rl-pilots/online-20260905-v1`.

The job script is `tools/online_rl_polaris.pbs`. Live startup logs confirmed
A100-40GB hardware, Java 21 and creation of the result directory. Final exit,
GPU memory, updates and reload must be recorded before declaring replication
complete. Existing Sophia evaluation job 178956 remains separate. The existing
30-minute monitor was updated with the actual RL job, scope and output path.

Completion: job 7593959 finished with PBS exit status 0 and wall time 00:02:14.
Its run is `online-rl-qwen-syntax-20260905-173201`. Two real optimizer updates
raised same-training-prompt keyword probability 0.892075 to 0.995756; sampled
SANY counts were 13, 16, 14, 16, 16 out of 16. Checkpoint reload logits matched
exactly. CUDA peak allocated memory was 2,403,588,608 bytes and peak reserved
memory 2,659,188,736 bytes. The result validates this small CUDA training path;
it establishes no full-spec generation or held-out prover improvement.

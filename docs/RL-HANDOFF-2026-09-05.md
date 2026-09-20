# RL execution handoff — 2026-09-05

> Historical handoff snapshot. Execution continued in the pinned task
> `Execute prover RL on Polaris and Sophia`. Read
> `docs/RL-EXECUTION-REVIEW-2026-09-05.md` and `docs/TLC-RL-2026-09-05.md`
> for current evidence. Polaris authentication was restored; syntax-RL job
> 7593959 completed successfully and TLC-RL job 7593992 was submitted.
> The "no RL job/checkpoint" statements below describe the handoff time only.

User explicitly requests verifier-driven RL training, actual compute execution,
fast turnaround on Polaris debug and the 64GB Mac, with Sophia also available.
They authorize subagents, fixes and job submission, and requested a new task to
own execution. Do not substitute another planning-only response or SFT-only
recommendation. Goal: improve the prover model toward 100% SANY, then TLC and
non-vacuity for applicable corpus populations. Never claim a guaranteed pass.

## Verified operational state

- Repository /Users/eric/GitHub/prove-TLA, branch board/193, dirty. Preserve all
  existing edits and raw results; work directly in this checkout to retain fixes.
- Sophia BatchMode SSH currently works. Only active account job is 178956,
  Q/no hold, by-gpu, pinned sophia-gpu-09. This is an evaluation serve job, NOT RL.
- Local tmux prove-tla-runner waits for 178956. Do not launch duplicate serving
  jobs or let competing tasks modify it. Decide explicitly how evaluation fits
  with the new training work.
- Last Polaris check: ssh -o BatchMode=yes -o ConnectTimeout=10 polaris failed
  Permission denied (keyboard-interactive,hostbased). User says Polaris has debug;
  debug limits/access have NOT been verified. Sophia has no debug queue. Check
  configured SSH/access, restore interactive authentication through the user if
  needed; continue local implementation while blocked. Do not invent access.
- No RL training job has been submitted by this task. No new trained checkpoint
  was produced. The only actual training recently run was toy smoke training.

## Existing RL design and required first actions

Read PLAN.md binding rules and docs/designs/2026-08-12-sany-tlc-grpo.md fully.
The latter is PROPOSED, not implemented/validated. It specifies survivor-corpus
generation prompts, holdout exclusion, G=8, verifier staircase rewards, entropy/
zero-variance/duplicate guards, and checkpointing. It flags 120B GRPO memory
feasibility as unproven and stale external rollouts as not strict on-policy GRPO.
Locate historical trainer/checkpoints in narrowly relevant local/remote code;
do not assume an RL trainer exists in this repository. Implement/adapt genuine
policy updates and test one optimization step locally, then a short real GPU
pilot in Polaris debug once access/queue limits are verified. Measure memory,
reward variation, KL/entropy, parameter change and checkpoint reload before a
longer run. Preserve harmony rendering and expert-LoRA coverage for gpt-oss.
Use subagents with distinct code scopes; main owns integration and actual launch.

Reward must retain SANY/TLC/non-vacuity, semantic-audit and population rules from
PLAN.md. Diamond is a separate corruption-repair measurement, not automatically
the next rung of a generation ladder. Do not reward infrastructure errors as
model mistakes or weaken gates. Train on allowed corpus, not holdout failures.

## Findings and changes already made

- docs/sany-diagnostic-2026-09-05.md: best single A/L run 28/30 SANY coverage;
  first attempt 40–47%; seed2 gaps128/148. A/L union30/30 does NOT establish
  single-policy100%. Error classes are syntax, operators, arity, etc.
- tools/sany_diagnostic.py uses gate-aligned dedup. Existing tools/staircase.py
  does not actually implement its claimed dedup; do not use it uncritically.
- tools/sany_repair_replay.py diagnostic8:5 SANY recoveries,1 TLC/nonvacuity pass.
  Regex lint can delete behavior; not enabled in production.
- tools/local_sany_pilot.py: real cached Qwen0.5B, offline MPS,2specs x2rounds,
  runs31.47s and23.2s. Both4 extraction failures; no SANY/TLC success. Raw outputs
  saved. Optional TLA_LOOP_EXTRACTION_FEEDBACK tested, not effective in tiny pilot.
- Job178712 crashed CUDA OOM at0.95/16. Safe serving script now
  tools/serve_vllm_w4dgm_safe.pbs deployed as ~/serve_vllm_w4dgm_safe.pbs on Sophia:
  0.90 GPU utilization,8 max sequences,TP8,32768 context; client concurrency8.
  Checkpoint /grand/EVITA/eric-spencer/chattla_artifacts/merged_w4dg_mech_120b.
- Runner now has mid-arm health watchdog, stops after two failures, uses safe
  script, concurrent8 startup probes with nonempty completion validation.
- Loop resume conservatively retries historical API-error keys on solved specs
  with original prompt/hash/provenance reconstruction.341 targets offline-checked.
  Seed2 remains1085 rows,341 effective historical errors pending live retry;
  seed3 has20 rows. Gates remain strict, evidence append-only.
- Full suite532 passed before last optional feedback test; targeted38 passed
  afterward. Smoke A–G passed. These are pipeline checks, not model accuracy.

## Monitoring ownership

Automation monitor-prove-tla-120b-evaluation runs every30min. Parent dispatches
gpt-5.3-codex-spark low for read-only checks and handles escalations. Heartbeat API has no
model override. Transfer its target to the new execution task and preserve quiet
routine checks, meaningful failure/completion notifications. New owner should
update prompt as real RL jobs are launched. No ChatTLA gate-25 adapter changes,
no publishing without passed gates.

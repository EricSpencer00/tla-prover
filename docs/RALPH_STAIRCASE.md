# Ralph loop: the staircase to 30/30

Started 2026-08-30, Eric-directed. Loop owner: the Claude session. This file is
the loop's working memory: state, roadblocks, and the decision ledger. Update it
every iteration. PLAN.md stays immutable; this file does not amend it.

## Goal (ordered, each rung on the frozen 30-spec holdout)

1. **100% SANY**: every holdout spec gets at least one SANY-passing candidate
   from the best honest system configuration.
2. **100% TLC (Gold)**: every TLC-graded spec gets a TLC-accepting candidate.
3. **100% Diamond**: every such candidate is non-vacuous (Rule-5 clean) and
   mutation-sensitive.

"System" means any honest configuration measured by the frozen harness: framing
L loop, grammar-constrained decoding, repair prompts, model choice. Weights may
change only with clean data (dataset-audit-2026-08-29). No redefinition of
"pass", no holdout edits, Rule-9 audit on every counted pass.

## Budget

Eric authorized up to **75% of the weekly usage allocation** (his /usage is
authoritative; he watches it). Proxy guard for the loop:
`python3 /Users/eric/.claude/skills/orchestrator/estimate-usage.py --days 7`
— STOP the loop and ping Eric when trailing-7-day weighted_mtok exceeds
**2600** (assumption: ~1.5x the 2026-08-29 heavy-week reading of 1729; Eric can
correct this number here). Also stop on: goal reached, or a roadblock only Eric
can clear (OTP, spend, outward-facing action) — ping Discord per
notify-eric-discord-otp and keep working on whatever does not block.

## Current state (2026-08-30, iteration 0)

- Best measured system: framing-L loop on UNTUNED base 120b, 17.3/30 mean
  (18/16/18). Tuned loop 12/30 (1 seed), tuned open 16/30 (1 seed).
- Tuned 2x2 seeds + grammar arm A5 queued: job 177470 (Sophia, still Q),
  runner tools/run_tuned_2x2_seeds.sh with reconnect logic, monitor armed.
- Failure taxonomy (3,836 SANY failures, 6 arms): 51% parse, 34% unknown
  operator (of which 1,990 invented operators, 1,195 qualified-vs-unqualified
  INSTANCE). Grammar tla_module_v1.ebnf: 0/438 false rejects, 86.7% offline
  catch rate — not yet measured in-loop (A5 does that).
- Never-solved specs across every arm (candidates from reachability data):
  13, 14, 55, 106, 121, 128, 132, 133, 135, 141, 148, 158 (verify against
  pooled ledgers in iteration 1).
- Holdout facts that bound the ceiling: 86 and 183 are byte-identical (the
  TLAPS module); 105 is a 428-byte stub; 4 library specs are SANY-only; 2
  proof modules are TLAPS-graded. So "30/30 TLC" is really 24/24 TLC-graded.
- RL staircase design exists (docs/designs/2026-08-12-sany-tlc-grpo.md) with
  the vacuous-pass rung amendment proposed (tier 2.5 at 0.85) — an option,
  not a commitment; the loop measures cheaper levers first.

## Iteration protocol

1. Integrate any finished arms (monitor events, gate-check, never
   summary.json).
2. Rebuild the per-spec staircase from ALL ledgers: for each holdout spec,
   deepest rung reached (SANY / TLC / vacuity-clean / diamond) and by which
   system. The gap list drives everything.
3. Pick the single highest-leverage intervention for the shallowest rung with
   gaps. Prefer measurements over training. Candidates, in rough order:
   grammar in the loop (A5 result), repair-prompt fixes for the
   unknown-operator classes, INSTANCE-qualification rewriting, per-spec
   autopsies of never-solved specs, chains/rounds budget shape, TLC-feedback
   verbatim quality in framing L.
4. Implement, run against the live serve (through the runner's ensure_serve
   pattern), score with gate-check, record here.
5. Usage check (guard above). Commit. Next iteration.

## Decision ledger

- 2026-08-30 it0: loop created. Waiting on job 177470 for the serve; grammar
  arm A5 is the first planned measurement.
- 2026-08-30 it1: built tools/staircase.py (all-ledger, per-spec deepest rung).
  **Generation-only (framing A/L) union frontier is 5 specs:** 55, 121, 141,
  148 stuck at sany-passes-but-TLC-never-accepts; 135 at tlc_vacuous. Rung-1
  (at least one SANY pass ever) is ALREADY 30/30 — "100% SANY" at union level
  is met; the per-sample rate is what starves the upper rungs. Pooled over
  framings including B-repair, 29/30 have passed (135 the lone holdout).
  Autopsies: 55 (MCEcho) and 135/141 (MCReachable/Reachable pair) have
  COMPLETE prompts post-signature-fix (checked build_generation_prompt
  output: N1/I1/R1 and LimitedSeq/ConnectedToSomeButNotAll all demanded);
  their TLC-error rows are pre-fix history. 135/141 candidates that reach TLC
  die "Invariant violated by the initial state" — the loop DOES feed the
  trace back (diagnose -> tlc_violation -> truncate_trace), but only 4-6 rows
  per ~480 ever get that far. 148 (Nano, 491 lines) is 425/480 sany=fail.
  121 runs on a MED-confidence draft cfg whose own comments say the finite
  bound really needs the spec-122 MC wrapper — feasibility question, one
  deeper autopsy owed before spending serve budget on it.
  **Conclusion: per-sample SANY yield is the shared bottleneck for all 5;
  the queued grammar arm (A5) is the highest-leverage pending measurement.**
  Usage guard: 1641.6 wMtok / 2600 — ok.

- 2026-08-30 it2: diagnosed the 31h queue stall — all schedulable prod nodes
  full, the three free nodes are inside standing reservation M177243, soonest
  full-node drain ~6h (177378). Moved the serve to 4 free GPUs on gpu-08:
  qdel 177470, new tp=4 by-gpu job 177494 (12h), runner repointed
  (SERVE_PBS/HOSTFILE tp4 variants, commit 2e5e4451). Half throughput, but
  arms start ~now; resume + the runner's resubmit cover the second window.
  A1-A4 then A5 run unattended once 177494 goes R.

- 2026-08-30 it3: spec-121 feasibility SETTLED by positive control — the
  canonical LeastCircularSubstring under the harness draft cfg passes TLC
  clean (218 distinct states, <1s, scratchpad/spec121). The cfg is fine; the
  failures are the model's. Root pattern found and it spans 121/135/141:
  canonical specs guard postconditions with `pc = "Done" => ...`
  (121.tla:161, 141.tla:194); models write them UNGUARDED, so TLC rejects at
  the initial state. Designed arm A6: in loop_eval.diagnose, when TLC reports
  "violated by the initial state", append one guidance line (invariant must
  hold in EVERY state incl. init; guard postconditions on termination).
  NOT implemented yet — the running 2x2 must finish under the current prompt
  or the seeds stop being comparable. A6 runs after A5. Serve 177494 still Q.
  Usage 1647/2600.

- 2026-08-30 it4: 177494 blocked on topology, not tags — PBS rewrites
  ngpus=4 chunks to require ngpu_quads=1, and gpu-08's 4 free GPUs do not
  form a free NVLink quad. tp=2 cannot hold 234GB of bf16 weights, so no
  smaller shape exists; the job places when a quad drains (earliest ~4h,
  177378's two nodes). Implemented A6 behind TLA_LOOP_INIT_HINT=1
  (commit 1d48c161, TDD: hint appends to frozen evidence, only on
  initial-state violations, byte-identical without the flag). Run order once
  the serve lands: A1-A4 (unchanged prompt), A5 grammar, then A6 with the
  hint flag vs the freshest loop control.

- 2026-08-30 it5: 148 (Nano) autopsy over 386 candidates: 0 truncated (all
  close their ==== bar; p50 7.5k chars vs canonical 17.9k), so max_tokens is
  NOT the constraint. SANY classes: 75 unknown-operator + pure parse tail
  (Encountered LET/,/|->/...). Conclusion: 148 needs no bespoke fix — its
  parse tail is the grammar arm's target class, and its under-modeling
  (candidates half canonical size) is the loop's. Frontier autopsies now
  complete for all 5 specs; every remaining intervention needs the serve.
  Iterations while 177494 sits in Q should be minimal status checks — do not
  spend budget re-deriving what this ledger already records.

- 2026-08-30 serve saga, resolved: tp=4 on shared nodes died deterministically
  twice (~9 min into worker init, gpu-06 then gpu-03, no worker traceback in
  the log) — burned jobs 177494/177523/177528 and ~12h of queue position;
  lesson recorded: this model serves ONLY on an exclusive 8-GPU node. 177524
  (SN config) came up clean. 12:09 preflight OK, and the enforcement probe
  PROVED structured outputs enforced (literal "alpha"; legacy guided_choice
  ignored) — A5 grammar-gated decoding is reachable for the first time.
  A1 launched 12:09. Expected: A1-A4 ~8.6h, A5 spills into a resubmitted
  window if the walltime ends (resume + runner handle it).

## Roadblocks

- (cleared it2) 177470's "No available resources": prod pool full + M177243
  reservation. Bypassed with the tp=4 serve on partial-node free GPUs.

## Roadblock 2026-08-31

- Sophia ControlMaster expired (~afternoon); all ssh now needs OTP. Discord
  ping sent. Runner treats it as "cluster unreachable" and retries forever,
  so nothing aborts. 177570 was still Q at last good poll. On re-auth the
  loop resumes with zero manual steps.
- Update: root cause is ALCF scheduled maintenance 2026-08-31 (all machines;
  Sophia 09:00-14:30 CT). Auth outage is facility-side; Eric's OTP is fine.
  Sophia queue drained to 0, so 177570 is likely purged -- runner resubmits.
  Resume polling after 14:30 CT.
- 2026-08-31 it6 -- BLOCKED, facility-side. Auth returned ~13:10 and Sophia
  left maintenance (19 jobs running, 45% usage, 11 nodes fully idle), but no
  job of ours can start. Evidence, in the order it was gathered:
  177570 came back Hold_Types=s "too many failed attempts to run"; qrls -h s
  is admin-only, so it was deleted and the runner resubmitted 177667, which
  was held the same way within one second, run_count=21. A minimal 6-line PBS
  script with the same resources (177669) held identically, which clears our
  serve script. Dropping filesystems=grand (177675) held identically, which
  clears the /lus/grand re-point onto an eagle clone. Allocation is healthy
  (EVITA 1,857.7 node-hours, expires 2026-09-20) and home is 28G/45G, so the
  "home over quota" note in memory is stale. Other users' jobs run fine on
  gpu-01..09. So: PBS places our job, the launch fails 21 times, PBS holds it.
  This needs an ALCF ticket -- Eric-only. Discord pinged.
  Runner stopped deliberately so it would not spend its last resubmit on a
  doomed job; all four held jobs and the probe scripts were cleaned up.
  Runner patched (this commit): job_state now reports a system hold as SHOLD
  and wait_for_job deletes it so the resubmit branch runs, because H was a
  wait state and would have hung forever on a job that can never start.
  Nothing about the staircase changed: A1 still holds 400 scored rows and the
  frontier is still the 5 specs from it1.

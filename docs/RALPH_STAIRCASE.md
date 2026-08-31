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

## Current state (2026-08-31, after iteration 23)

Read this block first; the decision ledger below is the evidence for it.

- BLOCKED on ALCF, not on work. Sophia places our jobs, the launch fails 21
  times in seconds, and PBS system-holds them (Hold_Types=s). A minimal 6-line
  PBS job reproduces it, the allocation is healthy and nodes are free, so it is
  facility-side and needs a ticket only Eric can file (it6). A probe
  (tools/sophia_start_probe.sh) submits one short job every 30 min and stays
  silent until one actually starts.
- The runner tools/run_tuned_2x2_seeds.sh now carries NINE arms unattended,
  A1-A9, and needs ~20.5h of serve against a 12h window (it23). It is stopped;
  relaunch with JOB=<new qsub id> once jobs can start.
    A1-A4  the tuned 2x2 seeds Eric committed to (A1 resumes at 400 rows)
    A5     decode-time grammar          A6  init-violation hint
    A7     no-redefinition prompt        A8  cfg interface/arity contract
    A9     wrapper-aware signature
  A6-A9 are all flag-gated and PROVEN append-only, so every frozen arm stays
  byte-identical. None of them has evidence it helps -- that needs a serve.
- What the frontier actually is. Rung 1 (>=1 SANY pass ever) is already 30/30;
  pooled over ALL framings 29/30 reach the summit, 135 alone stuck (it1, it9).
  But split by framing (it15), generation has NEVER solved a frontier spec:
  271 SANY-passing generations produced ZERO passing verdicts. The 29/30 comes
  from framing B, which repairs a corrupted GOLD spec -- an easier task. Any
  "29/30" claim must name its framing.
- Why generation dies. At SANY: parse 48%, unknown-operator 35%, redefinition
  27% of rows (it10). Half the unknown-operator class is scope errors a
  context-free grammar cannot see, so A5+A7 can reach at most 60% of frontier
  SANY failures even if perfect (it13, it14). At TLC: 55% of the 246 failures
  on SANY-clean generations are cfg INTERFACE mismatches -- wrong arity,
  undefined substitution target, a module the cfg names and the output lacks
  (it16). That is what A8 targets.
- A REAL HARNESS BUG, half-fixed. 5 specs (128, 141, 148, 158, 168) are checked
  through an MC wrapper that already provides names the prompt demands -- 17 of
  them, spanning constants, invariants and substitution targets. Demanding them
  again costs 190 rows to duplicate definitions (it19-it21). A8/A9 fix it
  behind flags; the DEFAULT prompt still has it, and fixing that changes
  prompt_sha256 for every wrapper spec, so it is Eric's call (asked, pending).
- Holdout facts that bound the ceiling: 86 and 183 are byte-identical (the
  TLAPS module); 105 is a 428-byte stub; 4 library specs are SANY-only; 2
  proof modules are TLAPS-graded. So "30/30 TLC" is really 24/24 TLC-graded.
- Grammar, measured exactly (it17): it rejects 722/923 = 78.2% of frontier
  parse-failing candidates. Projected cut in frontier SANY failures 38% -- but
  that counts rejection of text the model DID emit; under constrained decoding
  it emits something else, so it is not a promised gain.
- RL staircase design exists (docs/designs/2026-08-12-sany-tlc-grpo.md) with
  the vacuous-pass rung amendment proposed (tier 2.5 at 0.85) -- an option, not
  a commitment; the loop measures cheaper levers first.

## Waiting on Eric

1. File the ALCF ticket (text in Discord) -- nothing runs until jobs can start.
2. Decide whether the wrapper fix becomes the DEFAULT prompt or stays the A9
   arm. Default breaks byte-identity with every frozen arm.

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

- 2026-08-31 it7 (offline, cluster still blocked): A6 VALIDATED against real
  data, not just unit tests. Pulled every ledger row whose recorded TLC log
  contains "violated by the initial state" for the frontier specs: 13 rows
  (121, 135, 141, 148), all tlc=fail_invariant, sany=pass. Ran the real
  diagnose() on the real rows: with TLA_LOOP_INIT_HINT=1 the hint fires 13/13
  and the rung is tlc_violation; with the flag off it fires 0/13, and the
  unflagged evidence is a strict PREFIX of the flagged evidence in 13/13, so
  the frozen arms are provably unchanged. A6 is ready to run the moment a
  serve exists.
  Correction worth recording: the first attempt reported 0/13 and looked like
  an A6 defect. It was the test's fault -- the synthetic row omitted the `tlc`
  key that the branch gates on, so every log fell through to tlc_error. Re-run
  with the ledgers' own row dicts. Do not diagnose() with hand-built rows.
  Staircase re-run this iteration is unchanged: 29/30 pooled, 135 alone at
  tlc_vacuous.
- 2026-08-31 it8 (offline): A6 wired into the unattended sequence
  (run-id loop-w4dgm-120b-hint, same chains/rounds as A1/A2 so those are its
  control, placed last so no frozen arm ever sees the hint). The runner now
  covers A1-A6 end to end; when the cluster returns nothing needs a human.
  Usage guard 1623/2600 wMtok -- ok.

- 2026-08-31 it9 (offline): spec-135 autopsy CORRECTS how the staircase reads.
  135 sits at rung 3 (tlc_vacuous), which makes it look one step from the
  summit. It is not. Over 465 model-generation rows (41 oracle/corruption rows
  excluded): sany fails 348, TLC is reached and accepts exactly 1 = 0.22%.
  Six other tlc=pass rows for 135 are sample=None oracle/scorability runs on
  the GOLD spec -- they prove the task is scorable, and must never be counted
  as model progress.
  The single accepting candidate (loop-base-120b-seed2 c5r3) earns rung 3 by
  writing `TypeOK == TRUE`, `Inv1 == TRUE`, `Inv2 == TRUE`, `Inv3 == TRUE`,
  `PartialCorrectness == TRUE` -- every invariant stubbed to literal TRUE.
  So the rung-3 label rests on one gaming candidate, and the vacuity gate is
  doing exactly its job by refusing it.
  Consequence: 135's real frontier is the SANY rung, same as 55/121/141/148.
  This CONFIRMS it1 (per-sample SANY yield is the shared bottleneck) and
  removes 135 as a special case. Nothing here supports treating 135 as a
  vacuity problem.
  Hypothesis raised and NOT supported by this evidence, recorded so it is not
  silently assumed: A6's hint tells the model to guard postconditions with
  `pc = "Done" => ...`, and a guarded property is vacuously true if the spec
  never reaches Done, so A6 could in principle trade init-violations for
  vacuity failures. The one vacuous 135 candidate is a literal-TRUE stub, NOT
  a guard-induced vacuity, so it is no evidence either way. A6 already reports
  vacuity per row, so the check when it runs is: does A6 raise tlc_vacuous
  relative to its A1/A2 control.

- 2026-08-31 it10 (offline): frontier SANY failure mix measured per spec, and
  it both VALIDATES A5 and finds a class A5 cannot touch. Over the 2,324
  frontier SANY-fail rows (deduped, generation rows only): parse 48.0%,
  unknown_operator 35.0%, redefinition 10.7% (first-match classes), other 6.3%.
  Per spec the mix differs enough to change what helps:
    148  parse 74%  -> the grammar arm is exactly right for it
    121  parse 58%
    141  parse 46% / unknown-op 45%
    135  parse 36% / unknown-op 34%
    55   unknown-op 51%, parse 26%  -> the grammar helps 55 LEAST
  So A5 stays the right next measurement (parse is the plurality), but it is
  not the answer for 55.
  NEW CLASS, measured: counting rows that contain ANY redefinition error (not
  first-match), 630/2324 = 27.1% of frontier SANY failures, and 281 = 12.1%
  carry NO parse and NO unknown-operator error, so redefinition alone is what
  kills them. Spec 55 is 54% redefinition -- the very spec the grammar misses.
  Cause split over the top-18 redefined symbols (1,306 messages):
    cfg-constant declared AND defined            44%  (NoNode, R, Node,
                                                       initiator, Succ, ...)
    duplicate definition of a required operator  33%  (TypeOK, Init, Next,
                                                       Spec, AncestorProperties)
    standard-module clash                        17%  (Seq, Nat -- the module
                                                       EXTENDS the module that
                                                       already provides them)
    local/bound name                              6%
  IMPORTANT, so nobody "fixes" this redundantly: the prompt ALREADY says
  "the CONSTANTS as declared constants", and required_signature already drops
  standard-module names from the CONSTANTS list. So the gap is NOT a missing
  instruction in general; it is that nothing forbids (a) declaring and then
  also defining the same constant, (b) defining a name the EXTENDS'd standard
  module already provides, (c) emitting the same operator twice. Any A7 must
  target those three specifically and be flag-gated like A6, and it must be
  measured against a control -- a prompt line is not free, it can displace
  attention and cost accuracy elsewhere.

- 2026-08-31 it11 (offline): measured what the grammar would do ON THE
  FRONTIER, which is the number that predicts A5 -- the global 86.7% from it0
  is over the whole corpus and does not speak for these 5 specs.
  Method: for each frontier spec take a random sample (seed 0, n=25) of its
  parse-failing candidates and ask whether tla_module_v1 rejects the module
  region. Catch rate on parse failures: 141 92%, 55 84%, 148 80%, 121 76%,
  135 68%; overall 100/125 = 80.0%.
  Combined with it10's per-spec parse share, projected reduction in each
  spec's SANY failures: 148 59%, 121 44%, 141 42%, 135 24%, 55 22%; weighted
  over the five, 39%.
  CAVEAT that limits this claim: it measures whether the grammar would have
  REJECTED the text the model actually produced. Under constrained decoding
  those tokens are unreachable, so the model emits something else, which may
  or may not parse. This is the share of observed bad output the constraint
  blocks -- NOT a promised 39% improvement. A5 measures the real effect.
  Superseded work, recorded so it is not repeated: the full-corpus
  grammar_falsereject re-run was abandoned after ~40 min with no output. It
  re-derives a baseline it0 already has, and its per-reject diagnosis is
  char-by-char and very slow. The frontier-targeted script (/tmp, 68s) is the
  version worth keeping. My first attempt at it also wasted a run by piping
  through `tail` (buffered) under a 900s timeout, so it could never print.
- 2026-08-31 it12 (offline): A7 IMPLEMENTED, flag-gated behind
  TLA_PROMPT_NO_REDEF, and wired into the runner as a gen-eval arm with the
  A3/A4 shape so those are its control and it is directly comparable to A5.
  The block names only the three causes it10 measured (declare-then-also-define
  a constant 44%, a required operator defined twice 33%, clashing with a name
  the EXTENDS'd standard module provides 17%) rather than repeating the
  "declare constants" line the template already has. TDD: 3 tests, including
  one asserting the flagged prompt STARTS WITH the unflagged prompt, so the
  frozen arms are provably unchanged and any prompt_sha256 difference is
  attributable to this alone. Full suite 505 passed.
  The runner now carries A1-A7 unattended.

- 2026-08-31 it13 (offline): the unknown-operator class -- 35% of frontier
  SANY failures and 51% of spec 55 -- is NOT cheaply fixable, and that bounds
  what A5+A7 can do. 5,335 messages over the frontier split as:
    short local/bound name, i.e. a scope error   50%  (j 442, n 405, b 348,
                                                       i 303, k 234, pc 380)
    domain operator invented or omitted          40%  (Ledger, ReachableFrom,
                                                       Reachable, TC, ...)
    required operator referenced, never defined   7%  (TypeOK, Init, Next,
                                                       AncestorProperties)
    standard-module operator, EXTENDS missing     4%  (Cardinality etc.)
  Half of it is the model using a name outside the quantifier/LET that binds
  it, or using `pc` without declaring it. A context-free grammar cannot
  enforce scope, so A5 cannot touch this by construction, and a prompt line is
  unlikely to fix invented domain operators (another 40%) -- that is modeling
  competence, not instruction-following. Only the last 11% (omitted required
  definitions + missing EXTENDS) looks mechanically addressable, and it is
  small.
  CONSEQUENCE for the ladder: the tractable levers on the SANY rung are the
  grammar (parse, 48%) and A7 (redefinition, 27% of rows). The unknown-operator
  35% is a capability limit for this model, not a harness defect. Do not
  expect A5+A7 to reach 100% SANY; the honest ceiling is well short of it, and
  the remaining gap argues for the structural direction
  (structural-representation-direction memory) rather than more prompt work.
  Method note: the SANY message is "Unknown operator: `X'." -- backtick then
  apostrophe. A quote-agnostic regex silently matches nothing and reports an
  empty table, which is what my first pass did.

- 2026-08-31 it14 (offline): the CEILING on the SANY rung, computed per row.
  A row is reachable by A5+A7 only if every error it carries is parse and/or
  redefinition; one unknown-operator error puts it out of reach (it13: half of
  those are scope errors a context-free grammar cannot see).
    spec  sany-fail   A5+A7-reachable   blocked by unknown-op
     148        494        376 (76%)           104 (21%)
     121        461        341 (74%)           101 (22%)
     135        354        203 (57%)           120 (34%)
     141        459        224 (49%)           207 (45%)
      55        556        253 (46%)           281 (51%)
    frontier   2324       1397 (60%)           813 (35%)
  So even if A5 and A7 both worked PERFECTLY -- every parse error blocked and
  every redefinition prevented -- at most 60% of frontier SANY failures could
  become passes, and the real figure is lower because it11 measured the
  grammar rejecting only 69-80% of parse failures.
  This is the answer to "can prompt+grammar work reach 100% SANY on the
  frontier": no. It cannot, and the arithmetic says so before any serve time
  is spent. 55 and 141, the two hardest, are also the two least reachable
  (46% and 49%).
  It does NOT say A5/A7 are not worth running -- 60% of 2,324 rows is a large
  yield increase, and the ladder's rung 1 only needs ONE passing sample per
  spec. It says they will not close the rung alone, and the residual is the
  case for the structural direction rather than more instruction tuning.

- 2026-08-31 it15 (offline): THE FINDING OF THIS BLOCKED STRETCH, and it
  re-prioritises A5/A7. Splitting every frontier row by framing:
    framing A/L (generation)      framing B (repair from corrupted gold)
      spec  sanyOK  tlcOK  pass     spec  sanyOK  tlcOK  pass
        55      43      0     0       55      62     22    22
       121      34      0     0      121     150    109   109
       135     107      1     0      135   -- no rows at all --
       141      76      0     0      141     107     65     65
       148      11      0     0      148     123     71     71
  Generation produced 271 SANY-PASSING candidates across the five specs and
  ZERO passing verdicts. The single TLC accept is 135's invariant-stub (it9).
  Repair converts 35-73% of its SANY-passing rows into passes.
  What this corrects: it1 concluded "per-sample SANY yield is the shared
  bottleneck". For generation that is now falsified in the sense that matters
  -- when generation DOES clear SANY, TLC still rejects it every time, 271/271.
  Raising SANY yield buys more attempts at a wall generation has never once
  passed. A5 and A7 both raise SANY yield. They are still worth running (they
  are cheap, already built, and rung 1 needs only one passing sample), but on
  this evidence NEITHER should be expected to turn a frontier spec green, and
  the ladder must not be planned as if they will.
  Second consequence, about the 29/30 headline: the summit for 55/121/141/148
  is reached ONLY through framing B, which repairs a corrupted GOLD spec. That
  is a different and easier task than writing the spec from the description.
  Any claim of "29/30" has to say which framing produced it.
  Third: 135 is the lone unsolved spec partly because framing B was never
  applied to it -- the corruption step emits "skipped:no_valid_corruption" for
  135 in every B run (7 per run). So 135 is not measurably harder than the
  others under repair; it was never given the treatment that solves them.
  Next intervention this implies (needs a serve, so it is queued not run):
  attack generation's TLC wall, not its SANY yield -- the loop's repair rungs
  are what convert, and framing L already has them. Measure WHY 271 SANY-clean
  generations all die at TLC before spending more on decode-time constraints.

- 2026-08-31 it16 (offline): WHY the 271 SANY-clean generations all die at TLC
  -- and it is far more tractable than it15 feared. Of the 246 that reach
  tlc=error, the first TLC error line classifies as:
    cfg/module INTERFACE mismatch            136  55%
      arity mismatch                          64   "substitutes for Succ with
                                                    ConnectedToSomeButNotAll of
                                                    different number of
                                                    arguments" (and Seq/
                                                    LimitedSeq, 28)
      substitution target undefined           37   "substitutes for Node with
                                                    the undefined identifier NN"
      missing module or unassigned constant   26   "module name ZSequences is
                                                    not a module in the
                                                    specification" (spec 121),
                                                    "constant MaxChar is not
                                                    assigned a value"
    parsing/semantic failure on TLC's recheck  56  23%
    Java StackOverflowError (state explosion)  29  12%
    assumption evaluation failed or false      13   5%
  So the majority of generation's TLC wall is NOT bad modeling. It is the
  module failing to match the .cfg's interface contract: the model declares
  `CONSTANT Succ(_)` and then defines the substituting operator with no
  argument, or never defines it, or omits the module the cfg names.
  This REVISES it15's read. it15 was right that raising SANY yield alone will
  not turn a spec green, but wrong to imply the TLC wall is a capability
  limit. 55% of it is a mechanical interface bug of exactly the same family as
  A7 -- the model controls BOTH sides (it writes the CONSTANT declaration and
  the operator) and simply makes them inconsistent.
  PROPOSED A8 (not implemented; needs the same flag-gated + control treatment
  as A6/A7): state the arity contract in the prompt -- an operator substituted
  for a constant must take exactly as many arguments as that constant is
  declared with, the substitution target must actually be defined, and any
  module the .cfg names (ZSequences) must exist in the output. required_
  signature already parses the substitution pairs, so the data is in hand.
  Caveat before anyone counts this as 55%: these are FIRST error lines. Fixing
  the interface may just expose the next error in the same run, and 23% of the
  bucket is TLC's own parse recheck, which A5 addresses instead.

- 2026-08-31 it17: grammar census FINISHED (exact, no sampling) and A8 built.
  Census over all 923 frontier parse-failing candidates: 148 83%, 141 81%,
  55 80%, 135 77%, 121 69%; overall 722/923 = 78.2% (the n=25 sample said
  80.0%, so it was close). Re-projecting with exact rates: 148 62%, 121 40%,
  141 37%, 135 28%, 55 21%; weighted 38% of frontier SANY failures, versus
  39% on the sample. The it11 projection stands.
  A8 IMPLEMENTED behind TLA_PROMPT_ARITY, wired as a gen-eval arm with the
  A3/A4 shape (so those are its control, and it is comparable to A5 and A7).
  It names each substitution pair from the cfg and demands equal arity, that
  the target actually be defined, and that any module the cfg names exists.
  TDD: 5 tests including append-only and a silent-when-no-substitutions case;
  full suite 510 passed. Verified against spec 141's real cfg -- it emits the
  ConnectedToSomeButNotAll/Succ and LimitedSeq/Seq pairs by name.
  The runner now carries A1-A8 unattended.

- 2026-08-31 it18 (offline): A7 and A8 VALIDATED across all 30 holdout cfgs
  before any serve time is spent on them, since cfg handling is where this
  harness has broken before.
  Result: 30/30 build without exception; both blocks are append-only on every
  spec (so every frozen control stays byte-identical); A7 fires on all 30 (it
  is unconditional) and A8 on exactly 13, the specs whose cfg actually
  substitutes. Every backticked identifier A8 emits appears in that spec's own
  cfg -- 0 invented names, which was the specific risk of generating prompt
  text from parsed config.
  That 13/30 matches the gen-eval-cfg-substitution-bug memory exactly ("framing
  A under-specifies 13/30 holdout specs"), which is an independent check that
  the substitution parser sees the same population it did.
  A8 fires for ALL FIVE frontier specs, including 148 -- 148 has no builtin
  override but does carry `CalculateHash <- CalculateHashImpl`. So A5 (best on
  148, 83% catch) and A8 overlap there rather than dividing cleanly; the pair
  is complementary across the frontier, not disjoint.

- 2026-08-31 it19: found a REAL BUG by chasing it16's odd 23% bucket, and it
  would have made A8 actively harmful.
  The bucket was "Parsing or semantic analysis failed" on candidates SANY had
  already accepted -- 56 rows, all on 141 (45) and 148 (11). The lines before
  it read "Multiple declarations or definitions for symbol LimitedSeq ...
  duplicates the one in module Reachable". Cause: 5 holdout specs (128, 141,
  148, 158, 168) are checked through an MC wrapper, and 141's wrapper defines
  BOTH LimitedSeq and ConnectedToSomeButNotAll while 148's defines
  CalculateHashImpl -- exactly the substitution targets the .cfg names. SANY
  sees the candidate alone and passes; TLC parses candidate+wrapper together
  and rejects the duplicate.
  The existing prompt ALREADY tells the model to "ALSO define these operators,
  which the .cfg substitutes in", with no wrapper awareness -- build_generation_
  prompt never took a wrapper argument, though loop_eval.wrapper_text_for has
  existed for exactly this hazard and its own docstring warns it "would tell the
  model to define a name it must not define". So this is a pre-existing harness
  bug worth ~23% of the frontier's TLC failures, and my A8 as written in it17
  would have amplified it by demanding the same wrong thing more forcefully.
  FIXED for A8: _wrapper_defines() reads the wrapper's operator names, and the
  block now INVERTS for those -- "the wrapper ALREADY defines X: do NOT define
  it yourself". build_generation_prompt takes wrapper_text (default None, so
  nothing changes for callers that pass nothing), and both call sites now pass
  it. 2 new tests; full suite 512 passed. Verified on the real specs: 141 and
  148 now say do-NOT-define, 121 (no wrapper) still says define.
  NOT fixed, deliberately: the pre-existing "ALSO define these operators" line
  in _format_signature still ignores the wrapper. Correcting it changes the
  DEFAULT prompt and would break byte-identity with every frozen arm, so it
  needs its own flag-gated arm and Eric's call, not a silent edit.

- 2026-08-31 it20 (offline): scope of the it19 wrapper bug, measured across all
  5 wrapper specs rather than just the two frontier ones.
    spec  rows   wrapper-duplicate failures   wrapper defines
     168   706        94 (13%)                 1 operator
     158   706        44 (6%)                 10
     141   706        31 (4%)                  2
     128   706        20 (3%)                  1
     148   706         1 (0%)                 14
    TOTAL             190 rows
  A row counts here when its log shows a duplicate-definition error naming an
  operator its own wrapper defines. 168 is the worst hit and is not even a
  frontier spec, so the loss is spread across the holdout, not concentrated
  where it would have been noticed.
  Note the count differs from it19's 56: it19 filtered to sany=pass AND
  tlc=error on the 5 frontier specs; this counts any row on the 5 WRAPPER
  specs. Different populations, both correct for their question.
  Interesting non-correlation: 148's wrapper defines 14 operators but loses 1
  row, while 168's defines 1 and loses 94. The count of wrapper operators does
  not predict the damage -- what matters is whether the .cfg names that
  operator as a substitution target, which is what the prompt then demands.
  STATE: A8's path is fixed (it19). The DEFAULT path is not -- _format_signature
  still says "ALSO define these operators" with no wrapper awareness, so these
  190 rows keep being lost in any run without TLA_PROMPT_ARITY=1. Fixing the
  default changes every frozen arm's prompt_sha256, so it is Eric's call, not
  mine. Discord pinged.

- 2026-08-31 it21 (offline): the wrapper/prompt overlap is NOT limited to
  substitution targets, which matters for how big the default fix in it20 is.
  Names the prompt asks for that the wrapper already provides:
    158  10  MCAcceptor, MCBallot, MCQuorum, MCValue, ConsensusSpecBar,
             a1, a2, a3, v1, v2      <- model values and MC constants
    148   4  CalculateHash, CalculateHashImpl, SafetyInvariant, TypeInvariant
    128   1  MaxSeqLen
    141   1  ConnectedToSomeButNotAll
    168   1  n
  So the clash spans three categories, not one: substitution targets (what A8
  fixed), plain CONSTANTS, and INVARIANTS. 148 is the sharp case -- the prompt
  tells the model to define TypeInvariant and SafetyInvariant although the
  wrapper defines both, which is the "Error: The invariant TypeInvariant
  specified in the configuration file" line seen 6 times in it16.
  Caveat on reading these two iterations together: it20 counted OBSERVED
  failures (190 rows), this counts the SURFACE (17 name-clashes) -- a clash
  only costs rows when the model actually acts on it. 168's single clash on
  `n` produced 94 failures while 148's four produced 1, so surface size does
  not predict damage.
  158 is SANY-terminal (PROOF_MODULES), so TLC never runs on it and its 10
  clashes cost little; the damage concentrates where TLC does run.
  This sizes Eric's pending decision: the default fix is not a one-line change
  to the substitutions block. Doing it properly means _format_signature
  filtering constants, invariants and substitution targets against the wrapper,
  and it changes prompt_sha256 for every spec that has a wrapper.

- 2026-08-31 it22: A9 BUILT so Eric's it20 decision costs one line either way.
  _format_signature now takes wrapper_text and, behind TLA_PROMPT_WRAPPER_AWARE,
  filters wrapper-provided names out of constants, invariants, properties and
  substitution targets, then names them: "These names come from the
  model-checking wrapper and are already defined for you -- do NOT define or
  declare them". If Eric wants it as the default, drop the env check; if he
  wants it kept as an arm, it already is one (run-id wrapaware-w4dgm-120b,
  gen-eval shape so A3/A4 are its control).
  Byte-identity PROVEN, not assumed: with the flag off, passing the wrapper
  changes the prompt for 0/30 holdout specs. Verified on 148 with the flag on
  -- CalculateHash/CalculateHashImpl/TypeInvariant/SafetyInvariant drop out of
  the demanded list and move to the do-not-define line. 4 new tests, full suite
  516 passed.
  The runner now carries A1-A9.

- 2026-08-31 it23 (offline): verified the runner as a whole, not just its parts.
  Config check: all 5 env flags (TLA_LOOP_INIT_HINT, TLA_PROMPT_NO_REDEF,
  TLA_PROMPT_ARITY, TLA_PROMPT_WRAPPER_AWARE, TLA_GUIDED_GRAMMAR) appear in BOTH
  the runner and the code that reads them -- no silent typo, which is the way
  this project has lost runs before. All 9 run-ids are fresh except A1's
  deliberate 400-row resume, so no arm will silently resume someone else's dir.
  Timing, measured from ledger timestamps rather than guessed: a healthy loop
  arm is ~1.3h (loop-w4dgm-120b: 621 rows in 1.3h) and a gen arm ~2.9h
  (open-...-samesession: 960 rows in 2.9h). A1's own 10h for 400 rows and
  gate2-A's 20.4h are the SERIALIZED era before GEN_EVAL_CONCURRENCY=16, so
  they must not be used as the estimate.
  Consequence: the 9 arms need ~20.5h against a 12h window, crossing it at A7.
  The arms that would be starved are exactly A7/A8/A9 -- the newest ones,
  carrying the it16-it21 findings. Raised MAX_RESUBMITS 2 -> 4: the sequence
  needs 2 windows, and a resubmit can also be spent clearing a system hold, so
  2 left no slack. No reordering -- A1-A4 are the experiment Eric committed to
  and A1 is already 400 rows in.
- 2026-08-31 it24 (offline): consolidation, not new analysis. The ledger's
  "Current state" block still described iteration 0 (stale job 177470, a
  two-arm plan), which is the first thing the next session reads -- rewritten
  to the real state, with a "Waiting on Eric" section naming the two open
  decisions. Two memories written so the findings outlive this context:
  generation-vs-repair-framing (the 29/30 is framing B, generation has solved
  none) and mc-wrapper-prompt-bug (190 rows, default still broken).

- 2026-08-31 it25 (offline): the new arms EXERCISED end to end, not just
  unit-tested. Everything before this called build_generation_prompt directly;
  that never touched the real generator, and my it19 change put
  `from .loop_eval import wrapper_text_for` INSIDE gen_eval while loop_eval
  imports gen_eval at module level -- a circular-import hazard that unit tests
  on the prompt builder cannot catch.
  Checked: importing gen_eval first and loop_eval first both succeed. Then ran
  the real generator gen_eval_spec_framing_a("141", ..., k=0) against a fake
  model with all three flags on: 1 row produced, sany=pass, and the LIVE prompt
  the generator handed the model carries A7, A8 and A9, with A8 correctly
  inverted to "do NOT define it yourself" for 141's wrapper-provided operator.
  So the wiring works in the path the runner will actually take.
  Three of my own harness errors on the way, none in the shipped code: the fake
  model must return list[str] not list[tuple] and needs an `id`; cfg_dirs is
  [(label, path)] not [path]; and workroot/logdir must exist beforehand. Worth
  recording because the next person writing a dry-run will hit all three.
- 2026-08-31 it26 (offline): the LOOP path exercised end to end too, closing
  the symmetric gap to it25. it19 changed loop_eval's call site as well
  (wrapper_text is now passed there), and A6 is a loop arm, so verifying only
  the generation path left half the change unexercised.
  Ran loop_eval_spec("141", chains=1, rounds=2) against a fake model: 2 rows,
  2 model calls (generate then repair), first row sany=pass rung_in=generate,
  so the generate->diagnose->repair cycle completes. With the flags OFF the
  loop's generation prompt is unchanged even though wrapper_text is now passed
  -- byte-identity holds in the loop path, not just the gen path. With
  TLA_PROMPT_WRAPPER_AWARE and TLA_PROMPT_ARITY ON, the same prompt carries
  both blocks and A8 is correctly inverted for 141's wrapper operator.
  A6's hint branch was NOT hit here (the fake produces tlc=error, not
  fail_invariant); it was verified separately on 13 real init-violation rows in
  it7. Both halves are covered, by different means.
  Verification of the 9-arm runner is now as complete as it can be without a
  model: config, byte-identity, prompt content, both eval paths, timing budget.

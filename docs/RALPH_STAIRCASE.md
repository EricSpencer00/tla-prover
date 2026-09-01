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

## Current state (2026-08-31, after iteration 40)

Read this block first; the decision ledger below is the evidence.

- BLOCKED on ALCF since ~13:00. Sophia places our jobs, the launch fails 21
  times in seconds, and PBS system-holds them. A minimal 6-line PBS job
  reproduces it; allocation and nodes are fine. Facility-side, needs a ticket
  only Eric can file (it6). tools/sophia_start_probe.sh watches for recovery.
- The runner carries NINE arms unattended (A1-A9) and needs ~20.5h of serve
  against a 12h window, so MAX_RESUBMITS is 4 (it23). It is STOPPED; relaunch
  with JOB=<new qsub id> once jobs start. A1 resumes at its 400 rows.
- ALL FIVE new arms are verified as far as possible without a model: config
  flags, byte-identity with the flags off (0/30 specs differ), prompt content,
  both eval paths end-to-end, A8's arity guidance checked exhaustively against
  gold (20/20), A9 cross-checked against missing_signature (0 contradictions),
  and A5 shown to accept every frontier gold spec so it cannot make a target
  unreachable. Full suite 521 passing.
- FOUR OF THE FIVE NEEDED CORRECTING, and every correction came from reading
  real candidate text, not from tests: A6 hardcoded `pc = "Done"` when
  candidates spell it "done"/"terminated", which could have MANUFACTURED the
  vacuity it was meant to avoid (it34); A7 said "standard module" when 82 of
  55's 132 redefinition failures EXTEND Echo (it32); A8 pointed at the wrong
  side of the arity mismatch (it33) and then my own fix regressed the builtin
  case, telling the model to define LimitedSeq 0-ary and leaving the unbounded
  Seq that TLC cannot enumerate (it36); A9 contradicted missing_signature by
  filtering on declarations as well as definitions (it35). A5, the only arm
  derived mechanically rather than from belief, needed nothing.
- WHAT THE ARMS CAN AND CANNOT DO, measured before running them:
  A5+A7 reach at most 60% of frontier SANY failures (it14); A8+A9 at most 64%
  of the frontier TLC wall (it40). Neither closes its rung. No combination is a
  route to 30/30, which it15 already implied: across 2,373 frontier A/L rows --
  including framing L's own repair rounds -- generation has produced ZERO
  passing verdicts. The 29/30 summit is carried by framing B, which repairs a
  corrupted GOLD spec. Always name the framing.
- WHY 55 AND 135 RESIST, and it is structural. SIX of the 30 holdout specs are
  MC wrappers whose real content lives in a module the model never sees (13,
  14, 181, 133, 135, 55). 135 IS spec 141's wrapper. The per-spec solve rate
  tracks how many identifiers the .cfg demands from that unseen module: 181
  demands 1 and passes often, 135 demands 10 and never passes (it31). So
  "100% TLC on the frozen holdout" is partly ill-posed -- 135 cannot be earned
  honestly without changing the task or the mutation catalogue (it29-it30).
- A REAL HARNESS BUG, half-fixed: the prompt demands 17 names across the 5
  wrapper specs that the wrapper already provides, costing 190 rows to
  duplicate definitions (it19-it21). A8/A9 fix it behind flags; the DEFAULT
  prompt still has it.
- Holdout facts bounding the ceiling: 86 and 183 are byte-identical; 105 is a
  428-byte stub; 4 library specs are SANY-only; 2 proof modules are
  TLAPS-graded. "30/30 TLC" is really 24/24 TLC-graded.

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
- 2026-08-31 it27 (offline): sharpened it15's wording after reading the
  addendum, which reports "9 of 18 solves came from a repair round" -- a split
  WITHIN framing L, not the A/L-vs-B split it15 made. Calling A/L "generation"
  was loose, because L includes its own repair rounds.
  Re-checked with rung_in broken out. All 2,373 frontier A/L rows produce 0
  passing verdicts: A 1,701, L:sany 256, L:generate 192, L:signature 161,
  L:tlc_error 57, L:tlc_violation 6. So the claim SURVIVES and is in fact
  stronger than stated -- the loop's repair rounds are included and win nothing
  on these five specs, while framing B wins 35-73%. Both the addendum's
  statement and it15's are true; they cut the data differently and neither
  contradicts the other.
  Memory generation-vs-repair-framing corrected to say so, since as written it
  could have been read as "the loop never repairs anything", which is false.
- 2026-08-31 it28 (offline): does the wrapper bug depress a PUBLISHED number?
  Suggestive, and deliberately not claimed as more.
  Raw look: 4 of the 5 wrapper specs are among the 7 that never got a TLC pass
  under framing A/L (80% vs a 23% base rate). That is misleading -- 41, 128 and
  158 are SANY-terminal (a LIBRARY and two PROOF_MODULES), so they are not
  TLC-graded at all and cannot have a TLC pass by design.
  With those removed, over the 24 TLC-graded specs: wrapper specs without a TLC
  pass 2/3 (141, 148), non-wrapper 2/21 (55, 121). Fisher exact one-sided
  p = 0.061.
  CONCLUSION: n=3 wrapper specs is far too few. 2-of-3 is one spec away from
  1-of-3, and p=0.061 on that base is not evidence. The honest statement is
  that the two TLC-graded wrapper specs that carry a substitution the prompt
  demands (141, 148) are both unsolved under A/L, which is CONSISTENT with the
  190-row duplicate-definition cost measured directly in it20 -- but the direct
  row count is the evidence, not this spec-level association.
  So: no published number needs restating on this basis. What the addendum
  could fairly add is that generation results on the 5 wrapper specs are
  depressed by a harness defect, with it20's row count as the support.

- 2026-08-31 it29 (offline): WHY 135 is the lone unsolved spec -- it is not a
  system spec at all, and the task as posed is close to ill-formed.
  135.tla is 14 lines: `MODULE MCReachable EXTENDS Reachable`, defining exactly
  two helpers, ConnectedToSomeButNotAll and LimitedSeq(S). Reachable IS spec
  141 (243 lines), which defines all 7 identifiers 135's .cfg demands (TypeOK,
  Inv1, Inv2, Inv3, PartialCorrectness, Spec, Termination). So 135 is 141's
  MODEL-CHECKING WRAPPER, and 135/141 are two halves of one system.
  Consequences, all of which were previously separate puzzles:
  * The task for 135 is "write a module that provides TypeOK, Inv1, Inv2, Inv3,
    PartialCorrectness, Spec, Termination" -- but honestly those come from
    EXTENDS Reachable, which the model does not have. So the model either
    reproduces 243 lines of Reachable or stubs the invariants. it9 found the one
    TLC-accepted candidate did exactly the latter: every invariant `== TRUE`.
    That is the rational response to the prompt as given, not mere gaming.
  * Framing B can never run on 135: only 4 mutations exist (and_to_or,
    plus_to_minus, in_to_notin, cup_to_cap) and 135 has ZERO sites for three of
    them. Its only 3 `\in` are all BINDING positions -- `CHOOSE succ \in ...`,
    `\A n \in Nodes`, `CHOOSE len \in ...` -- where `\notin` is a syntax error,
    not a semantic corruption. Hence all 3 candidates rejected sany_fail, hence
    "no_valid_corruption" in every B run.
  * So 135 fails both routes for structural reasons: generation because the
    task under-determines a 243-line dependency, repair because the mutation
    catalogue cannot corrupt a 14-line wrapper.
  IMPLICATION for the goal ladder: "100% TLC on the frozen holdout" is not
  merely hard, it is partly ill-posed. 135 cannot be earned honestly without
  either giving the model Reachable (changing the task) or extending the
  mutation catalogue (changing framing B). Both are holdout-affecting decisions
  and therefore Eric's, not mine. Recorded, not acted on.

- 2026-08-31 it30 (offline): 135 is NOT a special case. SIX of the 30 holdout
  specs are MC wrappers -- short modules that EXTEND a non-standard module
  holding the real content:
    13 (7 lines, EXTENDS Bakery)      14 (8, Boulanger)
   181 (8, sums_even)                133 (14, ParReach)
   135 (14, Reachable = spec 141)     55 (36, Echo)
  55 is `MODULE MCEcho EXTENDS Echo` and defines only the test fixtures N1, I1,
  R1. It does NOT define TypeOK or AncestorProperties -- its .cfg demands them
  and Echo supplies them.
  This UNIFIES two findings that looked unrelated. it10 measured 55 as 54%
  redefinition, the highest on the frontier, with top symbols NoNode 228,
  R 172, TypeOK 118, AncestorProperties 113. Those are precisely the names the
  wrapper's own .cfg names and Echo already provides. So 55's redefinition rate
  is not model sloppiness; it is the task demanding names that the module it
  must EXTEND already defines -- the same shape as the it19 wrapper bug, one
  level up.
  So the two frontier specs generation never solves, 55 and 135, are BOTH MC
  wrappers, and the task for them is really "write a test harness for a spec
  you cannot see". That is a different and arguably unfair task from "write a
  spec from its description", and it is worth separating in any reporting.
  NOT acted on: reclassifying or re-scoping these 6 specs changes the frozen
  holdout, which is Eric's call. Recorded and pinged.

- 2026-08-31 it31 (offline): tested it30's claim as a POPULATION, with the
  non-wrapper specs as the control, rather than asserting it from two cases.
  Over TLC-graded specs (6 SANY-terminal excluded):
    WRAPPER (n=6)   A/L rows 2825, passes 89 = 3.2%, redefinition is 49% of
                    its SANY failures, 4/6 specs ever solved by A/L
    OTHERS  (n=18)  A/L rows 7796, passes 460 = 5.9%, redefinition 10%,
                    15/18 ever solved
  The redefinition signature is the strong result: 49% vs 10%, a 5x gap, and it
  is mechanistic rather than merely correlational -- it30 identified the actual
  clashing names (TypeOK, AncestorProperties, R, NoNode for 55) as the ones the
  EXTENDS'd module supplies. The pass-rate gap (3.2% vs 5.9%) points the same
  way but rows within a spec are correlated, so specs are the honest unit and
  n=6 is small; do not quote a p-value on it.
  IMPORTANT nuance that stops this being over-claimed: being a wrapper is NOT
  fatal. Per spec, A/L passes and identifiers the .cfg demands:
    181  8 lines,  1 demanded  -> 61/403 passes
     13  7 lines,  6 demanded  -> 26/477
     14  8 lines,  6 demanded  ->  1/513
    133 14 lines,  7 demanded  ->  1/454
     55 36 lines,  7 demanded  ->  0/513
    135 14 lines, 10 demanded  ->  0/465
  The gradient tracks HOW MUCH the .cfg demands from the unseen module, not
  wrapper-ness itself: 181 demands one identifier and passes often; 135 demands
  ten and never passes. So the real predictor is "identifiers the task requires
  that live in a module the model cannot see".

- 2026-08-31 it32 (offline): traced it31's predictor to the exact model
  behaviour, and it exposed a gap in MY OWN A7.
  Of 55's 132 candidates carrying a redefinition error, 82 write `EXTENDS Echo`
  (47 bare, 31 with TLC, 4 with Naturals) and then define names Echo already
  supplies. So the model correctly infers it should extend the system module,
  and the clash follows -- it is not failing to understand the task, it is
  hitting a contradiction inside it.
  A7 as written in it12 said "never define a name an EXTENDS'd STANDARD module
  already provides (for example Seq from Sequences, or Nat from Naturals)".
  Echo is not a standard module, so the rule as phrased missed the dominant
  real case -- the one it10 measured at 54% for this spec. Broadened to "any
  module you EXTEND", naming the Echo case explicitly. Test added that fails on
  the old wording; full suite 517 passed.
  This is why measuring the mechanism matters and not just the rate: A7 looked
  finished at it12 and was aimed slightly off the thing it was built for.

- 2026-08-31 it33 (offline): applied it32's lesson to A8 and found the SAME
  class of error -- my instruction was aimed at the wrong side of the mismatch.
  What the 57 arity-mismatch candidates actually wrote: `CONSTANT Succ` with no
  arity 55 times, while defining `ConnectedToSomeButNotAll(n)` WITH a parameter
  35 times (and 0-ary 14 times). So the constant declaration is usually RIGHT
  and the operator definition is wrong.
  Which is correct: 141 uses `Succ[n]` -- square brackets -- so Succ is a 0-ary
  constant HOLDING A FUNCTION, and gold 135 defines `ConnectedToSomeButNotAll
  ==` with no parameter. The model's error is confusing "holds a function" with
  "takes an argument".
  A8 as written in it17 said "if you write `CONSTANT Succ(_)` then
  `ConnectedToSomeButNotAll` takes one argument" -- which points at the 1-ary
  reading, the wrong one for the dominant case, and could have pushed models
  toward the error it was built to prevent.
  Rewritten: a plainly declared constant is 0-ary EVEN IF it holds a function
  applied with square brackets, so write `X == ...` not `X(x) == ...`; only
  `CONSTANT L(_)` takes an argument. Test added; full suite 518 passed.
  Two of my three prompt arms were aimed slightly wrong and only reading the
  actual candidates caught it. Rate measurements said WHICH class to attack;
  they could not say what to say about it.

- 2026-08-31 it34 (offline): checked A6 the same way, and it had a subtler
  version of the same defect -- one that could have CAUSED the failure it9 went
  looking for.
  Of the 13 candidates behind real init violations, 12 do have a `pc` variable,
  so A6's framing is applicable. But their terminal state names vary: "done"
  12, "Done" 9, "terminated" 4. A6 hardcoded the literal `pc = "Done"`.
  A model whose own terminal value is "done" can copy the literal, producing a
  guard that NEVER holds -- and an invariant guarded by an impossible antecedent
  is vacuously true, which the Rule-5 gate rejects. So the hint could have
  manufactured exactly the vacuity failure it9 hypothesised and found no
  evidence for. it9 recorded that hypothesis as unsupported; this is the
  mechanism by which it could have become true.
  Rewritten to point at "the value your control variable actually takes when
  the algorithm has finished, written exactly as you spell it in this module",
  with an explicit warning not to copy a terminal-state name from elsewhere and
  a note that an unsatisfiable guard is rejected as vacuous. Test added that
  fails on any hardcoded literal.
  Re-verified on the 13 real rows after the rewrite: still fires 13/13 with the
  flag and 0/13 without. Full suite 519 passed.
  Tally for this stretch: ALL THREE prompt-side arms (A6, A7, A8) were aimed
  wrong in a way only reading real candidate text exposed. The rate
  measurements chose the targets correctly; none of them could say what to
  write.

- 2026-08-31 it35 (offline): A9 checked too, and it had a DIFFERENT defect --
  it contradicted the harness's own criterion.
  A9 filtered on _wrapper_provides, which counted names the wrapper merely
  DECLARES as well as those it DEFINES. On spec 148 that made A9 tell the model
  to omit CalculateHash, while missing_signature -- which is wrapper-aware and
  is the harness's own pass criterion -- still requires the candidate to supply
  it. An obedient model would have been marked signature-incomplete and the
  loop would have demanded back exactly what A9 told it to drop.
  Narrowed A9 to _wrapper_defines (== definitions only): a constant the wrapper
  declares does not relieve the candidate of declaring its own. Re-checked
  across all 5 wrapper specs by simulating an A9-obedient candidate and running
  missing_signature on it: contradictions 0, was 1. 148 now correctly omits
  only SafetyInvariant and TypeInvariant, which the wrapper really defines.
  One earlier test asserted the old, wrong behaviour (that a declared-only
  constant is dropped); updated to the corrected rule rather than deleted, so
  the distinction stays pinned. Full suite 520 passed.
  All four new arms have now been mechanism-checked against real data, and ALL
  FOUR needed correction: A6 hardcoded a terminal literal, A7 said "standard
  module" when the real case was any module, A8 pointed at the wrong side of
  the arity mismatch, A9 contradicted missing_signature. Unit tests passed for
  every one of them beforehand.

- 2026-08-31 it36 (offline): opened the last unexamined bucket from it16 -- the
  29 Java StackOverflowError rows -- and it exposed a THIRD aiming error in A8,
  this one introduced by my own it33 fix.
  The 29 rows are 100% in the two wrapper specs (135: 20, 55: 9), and 18 of the
  29 candidates use `Seq(`. `Seq(S)` from Sequences is the set of ALL finite
  sequences -- infinite, so TLC cannot enumerate it. That is exactly why gold
  135 defines the BOUNDED `LimitedSeq(S)` and the .cfg substitutes
  `Seq <- LimitedSeq`.
  But `Seq <- LimitedSeq` is a BUILTIN override, not a declared constant, and
  it33's correction applied constant-declaration logic to it: A8 was emitting
  "a constant declared plainly (`CONSTANT Seq`) is 0-ary ... so write
  `LimitedSeq == ...`, NOT `LimitedSeq(x) == ...`". Gold defines
  `LimitedSeq(S)` -- ONE argument, matching Sequences' own Seq(S). So A8 was
  telling the model to break the substitution, which leaves the unbounded Seq
  in place: the very StackOverflow this bucket is made of.
  Fixed by splitting builtin overrides from constant substitutions and stating
  the STANDARD operator's own arity (_STANDARD_ARITY: Seq 1, Nat 0, Cardinality
  1, ...). 141 now reads "`LimitedSeq` replaces `Seq` from Sequences, which
  takes one argument, so write `LimitedSeq(S) == ...`"; 121 reads "`CharacterSet`
  replaces `Nat` from Naturals, which takes no arguments". Test added; one older
  test pinned the superseded wording and was updated. Full suite 521 passed.
  Note against myself: it33 was a correct fix for the Succ/constant case and a
  regression for the Seq/builtin case. A fix aimed by one example can break the
  case it did not look at -- the two kinds of substitution needed separate rules
  from the start.

- 2026-08-31 it37 (offline): stopped finding A8's aiming errors one at a time
  and checked ALL of them at once. For every substitution target A8 names
  across the 30 holdout cfgs, compared the arity A8 demands against the arity
  the corpus ACTUALLY defines that operator with.
  20 targets checked. On the production path -- wrapper_text passed, as
  gen_eval does -- MISMATCHES: 0.
  One apparent mismatch, spec 148's CalculateHashImpl (gold arity 3 in 147.tla),
  came from my own check calling _arity_block WITHOUT the wrapper. With the
  wrapper, 148 correctly emits "the wrapper ALREADY defines
  CalculateHashImpl: do NOT define it yourself" and never states an arity at
  all. So the finding was a flaw in the verification, not the code -- worth
  recording because it is the third time this session a check has been wrong in
  a way that looked like a bug (see it7's synthetic rows and it13's regex).
  A8's arity guidance is now verified complete against gold rather than
  spot-checked, which is what should have been done at it17 instead of three
  successive single-example fixes.

- 2026-08-31 it38 (offline): re-ran the 30-spec validation as a REGRESSION
  check, because it18's version predates every correction from it32-it36 and
  those touched the code paths it was validating.
  All 30 holdout specs, all 3 prompt flags, with wrapper_text passed as
  production does. Problems: 0. Specifically: no exceptions, A7 and A8 remain
  strictly append-only, and no emitted block names an identifier that appears
  in neither the spec's .cfg nor its wrapper -- the invented-name check that
  matters when prompt text is generated from parsed config.
  Coverage is now visible and matches intent: A7 fires for all 30 (it is
  unconditional), A8 for 13 (the specs whose .cfg substitutes), A9 for 5 (the
  wrapper specs). Those are exactly the populations each arm was built for, and
  the 13 again matches the gen-eval-cfg-substitution-bug memory.
  A9's change is not append-only by design -- it FILTERS the signature block --
  so it is checked differently, by prompt-head stability plus the it35
  missing_signature consistency test, not by a startswith assertion.

- 2026-08-31 it39 (offline): A5 mechanism-checked too, and it is the ONE arm
  that needed no correction.
  The decisive safety question for a decode-time grammar is not its catch rate
  but whether it can still express the target. Checked directly: tla_module_v1
  ACCEPTS the gold spec of all five frontier specs (55, 121, 135, 141, 148) and
  both wrapper dependencies (135/MCReachable, 147). So constraining decoding to
  this grammar does not make any frontier target unreachable. A rejection here
  would have made A5 actively harmful on exactly the specs it targets.
  Contrast worth keeping: A5 is derived MECHANICALLY -- an EBNF validated
  against real specs, with a measured false-reject rate -- and it was aimed
  correctly from the start. A6-A9 encode my beliefs about what to TELL the
  model, and all four were mis-aimed until checked against real candidate text.
  The failure mode is not "prompts are unreliable"; it is that a mechanical
  artefact carries its own falsification (does the grammar accept the gold?)
  while a sentence of advice does not, so its correctness has to be imported
  from data deliberately.
  All five arms are now verified as far as they can be without a model.

- 2026-08-31 it40 (offline): the CEILING for the TLC-rung arms, the analogue of
  it14's SANY-rung ceiling, so A8/A9 have an honest expectation before they run.
  Of the 246 TLC failures on SANY-clean frontier generations:
    interface mismatch (A8's target)      126  51%
    wrapper duplicate  (A9's target)       31  13%
    state explosion (StackOverflow/OOM)    29  12%
    parse recheck, independent of dup      25  10%
    assumption failed or false             13   5%
  Rows whose ONLY problem is interface or duplicate, and are therefore
  reachable by A8+A9: 157/246 = 64%.
  So even if both arms worked perfectly, about a third of this wall remains --
  state explosion, failed assumptions and TLC-side parse failures need
  something else. And 64% of the wall is not 64% of specs: clearing a row's
  first error can simply expose its next one, which is why it16 flagged that
  these are FIRST error lines.
  Put beside it14 (A5+A7 reach at most 60% of frontier SANY failures), the
  honest summary of all five arms is: they address the majority of both walls
  and neither one completely, and no combination of them is a route to 30/30 on
  the frontier. That was already implied by it15 (generation has never once
  solved these specs) and it29-it30 (55 and 135 are MC wrappers whose task is
  under-determined); this quantifies it for the TLC rung specifically.

- 2026-08-31 it41 (offline): verified the RECOVERY PROBE itself, because a
  monitor designed to stay silent while broken cannot be distinguished from a
  monitor that has died -- its silence is not evidence of anything until
  checked.
  It is genuinely working: 3 probe jobs really were submitted (177693, 177757,
  177773). Each reached Hold_Types=s with run_count=21 -- the same instant
  system hold as everything else -- and the probe deleted it, so the cluster is
  still broken and the silence is correct.
  Also checked that it WOULD fire: its awk classifier returns HELD (silent)
  only for job_state=H with a system hold, and reports for R, Q and F.
  Nuance, recorded rather than "fixed": firing on Q means "the instant-hold bug
  is gone", not "the job ran". That is the right trigger anyway -- the runner
  handles Q by waiting, and if a job is held later the it19 SHOLD path deletes
  and resubmits within budget. So an early fire degrades gracefully.
  Caveat on coverage: the probe process shows ~72 min elapsed, not the ~6h
  since I armed it, and 3 submissions at INTERVAL=1800 matches ~72 min. So it
  restarted at some point and there is a gap where nothing was watching. It is
  watching now; if the cluster recovered during that gap, the next probe within
  30 min catches it.
- 2026-08-31 it42 (offline): fixed the weakness it41 exposed in my own
  monitoring. The probe now appends a timestamped line every cycle to
  results/runs/sophia_probe.log, so coverage is READ rather than guessed from
  process elapsed time. Restarted it (the running instance predated the change)
  and confirmed the log is being written.
  This matters because the probe is the thing that decides when the whole
  9-arm sequence restarts. A silent-while-broken monitor with no heartbeat can
  fail closed and nobody notices; with the log, a gap is visible after the fact
  instead of inferred.

- 2026-08-31 it43 (offline): opened the last unexamined bucket and found BOTH a
  new failure cause and an error in my own it40 classification.
  (a) CLASSIFICATION ERROR: it40 detected wrapper duplicates with "Multiple
  declarations"/"duplicates the one at". SANY also words it "Multiply-defined
  symbol" and "already defined or declared", which it40 missed -- 4 of the 56
  parse-fail rows were mis-bucketed as independent parse failures when they are
  duplicates. Small (it does not move the 64% ceiling materially) but it is the
  second time a text-matching filter of mine has under-counted (see it13's
  quote-agnostic regex). Recorded so the number is not re-quoted as exact.
  (b) NEW CAUSE, and it is another invisible wrapper contract: 28 of the 56
  parse-fail rows show "Unknown operator: `Cardinality'" raised INSIDE the
  wrapper module, not the candidate. Gold 135/MCReachable calls Cardinality,
  and it only resolves because gold 141/Reachable EXTENDS FiniteSets and the
  wrapper inherits it. When the model's Reachable omits EXTENDS FiniteSets, the
  CANDIDATE still passes SANY on its own -- and the WRAPPER fails to compile.
  So the candidate is penalised for an operator it never used, required by a
  module it never sees. Nothing in the prompt says the wrapper needs it.
  This is the same family as it19-it21 (the prompt is blind to the wrapper) but
  the opposite direction: there the prompt demanded names the wrapper SUPPLIES,
  here it stays silent about names the wrapper REQUIRES. A complete fix has to
  handle both directions.
  NOT implemented: an A10 would state the operators the wrapper needs from the
  candidate. It is derivable -- parse the wrapper for free identifiers and
  intersect with the standard modules. Recorded rather than built, because
  four of my five arms were mis-aimed on first writing and this one deserves
  the same evidence-first treatment rather than being added late and untested.

- 2026-08-31 it44 (offline): did the EVIDENCE for A10 before writing any prompt
  text, which is the discipline it32-it36 taught. It took three tries to get
  the derivation right, and every error was mine.
  Goal: derive, per wrapper spec, which standard-module operators the WRAPPER
  uses that the CANDIDATE must supply -- the it43 cause, where the wrapper
  fails on `Unknown operator: Cardinality` although the candidate never used it.
  Validation rule: the derivation is only trustworthy if the GOLD candidate
  already provides what it claims is needed.
    attempt 1  4/5 -- claimed 148 needs FiniteSets. FALSE: wrapper 147 EXTENDS
               FiniteSets itself, on a MULTI-LINE clause my single-line regex
               truncated to ['', 'Naturals'].
    attempt 2  3/5 -- the multi-line regex used `\s+` for continuations, which
               crosses blank lines and swallowed `CONSTANT Root` into the last
               token, so 141's FiniteSets stopped matching.
    attempt 3  5/5 -- continuation only while a line ends with a comma, stopping
               at a blank or unindented line. Unit-tested on four EXTENDS shapes
               BEFORE being trusted.
  Result, validated 5/5 against gold: 128 needs Sequences (wrapper uses Seq),
  141 and 168 need FiniteSets (Cardinality), 148 and 158 need nothing -- their
  wrappers extend what they use.
  So an A10 is now derivable correctly. NOT built: the cluster is still down, no
  arm can be measured, and a tenth untested arm adds risk without information.
  The derivation and its validation are recorded so it can be built with
  evidence rather than belief when there is something to measure.
  Note: it30's wrapper-shaped scan used the same single-line EXTENDS regex. Its
  conclusion is unaffected -- those six specs have single-line clauses -- but
  the helper there is the flawed one.
- 2026-08-31 it45 (offline): verified the it30 claim I had only ASSERTED. it44
  noted that it30's wrapper scan used the flawed single-line EXTENDS regex and
  I stated its conclusion was unaffected -- without checking. Re-ran the scan
  with the corrected, unit-tested parser: the six wrapper-shaped specs are
  IDENTICAL (13, 14, 55, 133, 135, 181). The claim holds, but it holds because
  it was checked, not because I said so.
  Worth keeping as a habit note: "the bug does not affect this other result" is
  itself a claim, and it costs one command to test.
- 2026-08-31 it46 (offline): wrote the session's transferable lesson to memory
  (prompt-arms-need-mechanism-checks) so the next arm is not built the same way:
  all four prompt-side arms passed their tests and were still mis-aimed; only
  reading real failing candidates caught it; A5, the one mechanical arm, needed
  nothing. Includes the four-step check to run before any prompt arm, and the
  warning that my own verification scripts were wrong three times this session.
  Probe healthy: heartbeat at 14:44 state=HELD, next cycle due 15:14.

- 2026-08-31 it47 (offline): final state verification, since the analysis is
  exhausted and what matters now is that this hands off cleanly.
  * All my work is committed. The only modified file is
    tools/w4_recall_audit.py, which is NOT mine -- it was modified at 07:23,
    before this session's work, and every commit here named explicit paths
    rather than `git add -A` on the tree, precisely so it stayed untouched. It
    is still uncommitted and unaltered, waiting for whoever owns it.
  * The runner parses and carries all nine arms in order: A1/A2 loop seeds,
    A3/A4 open seeds, A5 grammar, A6 init-hint, A7 no-redef, A8 arity,
    A9 wrapper-aware.
  * Probe healthy and logging every cycle.
  TO RESUME when Sophia accepts jobs: qsub ~/serve_vllm_w4dgm_sn.pbs, then
  `JOB=<id> PORT=8321 nohup bash tools/run_tuned_2x2_seeds.sh &`. A1 resumes at
  its 400 rows; nothing else needs a human.

- 2026-08-31 it48: REORDERED the optional arms by measured target size, because
  the order was by arm number and the serve window starves whatever runs late.
  The nine arms need ~20.5h against a 12h window (it23), so position matters.
  A6 -- the SMALLEST target of all, 11 init-violation rows on the frontier --
  was running 6th, ahead of A7, A8 and A9, each of which targets a class an
  order of magnitude larger.
  New order after the frozen A1-A4: A8 (51% of the 246 TLC failures), A7 (27%
  of SANY-fail rows), A5 (48% parse at 78.2% catch), A9 (13% of TLC failures
  plus the 190-row wrapper bug), A6 last.
  Verified after the move: script parses, all nine arms present in the new
  order, and A5's `if [ "$GRAMMAR_OK" = 1 ]` guard moved intact with its else
  branch -- if/else/fi still pair 1/1/1. That guard is the one that must not be
  lost: it exists because vLLM accepts the legacy guided_* names with HTTP 200
  and silently ignores them, so an unguarded A5 would look like it ran.
  A1-A4 deliberately unmoved: they are the experiment Eric committed to and A1
  already holds 400 rows.
  A10 NOT added, and the scheduling is the reason rather than the evidence --
  its derivation is validated 5/5 (it44), but a tenth arm makes the sequence
  ~23.4h and would itself be the starved one. It belongs in a second batch, or
  in place of A6.
- 2026-08-31 it49 (offline): checked what it48's reorder actually buys, and it
  is narrower than "the arms are better ordered now".
  Arms completing inside a single 12h window:
    old order  A1 A2 A3 A4 A5 A6   (6 arms, 11.8h)
    new order  A1 A2 A3 A4 A8      (5 arms, 10.5h)
  So the reorder moves A8 -- the largest measured target, 51% of the TLC
  failures -- into the first window, at the cost of A5 and A6 moving out, and
  fits one FEWER arm there.
  Whether that is an improvement depends entirely on something I should state
  rather than assume: with MAX_RESUBMITS=4 the sequence spans ~2 windows and
  ALL nine arms run regardless, so order only matters if the run is cut short
  -- a failed resubmit, a re-broken cluster, or Eric stopping it. The reorder
  is insurance against early termination, not a throughput gain, and it is a
  mild net loss in arms-per-window if nothing goes wrong.
  Keeping it: this stretch has already seen the cluster break mid-sequence
  twice (the tp=4 deaths, then the system hold), so early termination is the
  case worth insuring against. But "ordered by value" overstated it -- the
  honest claim is "the largest target is no longer behind two smaller ones if
  the run is interrupted".

- 2026-08-31 it50: ROOT CAUSE ISOLATED by bisection, no ticket needed to find it.
  **8-GPU (whole-node) allocations fail to start for our account; 4-GPU
  allocations run fine.** Verified: `select=1:ngpus=4:ncpus=128:mem=480gb -q
  by-gpu` reached state R in 20s with run_count=1 on sophia-gpu-07 and produced
  output. Every ngpus=8 request holds at run_count=21.
  Ruled out one variable at a time: queue (single-node, by-node, by-gpu all fail
  at 8), placement (scatter:excl, shared, free), filesystems (home, eagle,
  grand, home:eagle:grand), the `system=sophia` select tag another user's
  working job carries, resource shape (ncpus/mem make no difference -- the
  submit hook rewrites everything to a whole node anyway), project allocation
  (EVITA healthy, 1857 node-hours), home permissions, login shell, and output
  paths. A full attribute diff against a RUNNING 8-GPU job (177582, user
  xiaolongm) shows no configuration difference at all -- only runtime fields.
  Two doors that are shut: the submit hook rejects multi-chunk GPU requests
  ("ambiguous select request"), so 2x4 GPUs across nodes is not expressible;
  and the infer-svc queue is ACL'd to openinference_svc.
  HARDWARE CORRECTION, and it matters: the nodes are **A100-SXM4-40GB**, not
  80GB as alcf-sophia-native-training memory says. So a node is 320GB of GPU
  memory and 4 GPUs is 160GB. The merged bf16 120b (~234GB) genuinely needs 8,
  which is why tp=4 died before -- that was not a serving bug, it was OOM.
  MECHANISM, traced the rest of the way (it50 cont.): the idle nodes are the
  problem. gpu-10..22 show state=free, queue_tags=prod, ngpus=8, 0 assigned --
  and are NOT schedulable: a job pinned to gpu-12 sits queued with "Insufficient
  amount of resource: queue_tags" while the identical job pinned to gpu-07 runs.
  A full pbsnodes diff of the two shows no difference beyond identity fields.
  So something invisible to us holds those nodes (the standing reservation from
  it2 is the obvious candidate; pbs_rstat returns nothing for our account).
  That explains the whole symptom: an 8-GPU job can only be placed on a fully
  idle node, every fully idle node is unavailable, so PBS tries, fails 21 times
  and system-holds. It is not our script, our project, or our request.
  What still works: BACKFILL onto partially-used nodes, and only for very short
  jobs -- a 5-minute 4-GPU job ran instantly on gpu-07 (run_count=1), while the
  same job at 15 minutes and at 1 hour just queues. The running jobs are 24h
  jobs about 3h in, so ordinary capacity returns in roughly 21h.
  CONSEQUENCE: no serve is possible right now, and this is not fixable from the
  user side. Left queued: 177829, a 4-GPU fp8 serve (tp=4, --quantization fp8,
  8192 ctx) which starts by itself when capacity appears. It is a FALLBACK, not
  a substitute -- fp8 changes the weights, so its numbers are not comparable to
  the frozen bf16 arms; it would need its own matched control, and A1/A2 in
  particular must stay bf16 to be comparable to seed 1.

- 2026-08-31 it51: the capacity picture completes the diagnosis, and the job is
  now "fixed" in the only sense available to us -- a valid configuration is
  queued and will start by itself.
  Sophia is split in two: gpu-01..09 are schedulable and now FULL (gpu-05/06/07
  went from 4 free GPUs to 0/0 while I was testing, which is why a 5-minute job
  that ran instantly an hour ago now queues), and gpu-10..22 are idle but NOT
  schedulable. Nothing of ours can start until the running 24h jobs end -- they
  were ~3h in, so roughly 21h -- or the idle nodes are released.
  So the earlier "8-GPU is broken" framing was half right: 8-GPU jobs fail
  because the only nodes that could host them are the unschedulable ones. It is
  a capacity/reservation problem wearing a launch-failure costume.
  Left queued: 177829, 4 GPUs, fp8, tp=4, 8192 ctx, 2h walltime. It starts
  automatically when gpu-01..09 free up. Its host lands in
  ~/vllm_serve_host_w4dgm_g4.txt (NOT the _sn.txt the runner reads), so pointing
  the runner at it is a deliberate act, not an accident.
  The comparability caveat stands and is the reason this is a fallback: fp8
  changes the weights. A1/A2 must stay bf16 to compare with seed 1, so the 2x2
  still needs 8 GPUs. The intervention arms could run fp8 IF their control
  (A3/A4) is re-run fp8 too -- internally valid, not comparable to the frozen
  baselines.

- 2026-08-31 it52: built and STARTED tools/sophia_autoserve.sh, which is the
  actual fix available to us. It polls every 10 min for a SCHEDULABLE node
  (gpu-01..09) with all 8 GPUs free and submits the bf16 serve only then.
  Submitting into the current state is what produces the unrecoverable system
  hold; waiting for real capacity turns that into an ordinary queue wait. If a
  submitted job holds anyway it deletes it and keeps watching, so a wrong
  capacity read costs nothing. Running as monitor b4p4hu3x1, logging each poll
  to results/runs/sophia_autoserve.log.
  Its detection was WRONG on first writing and I caught it with a positive
  control: the node-header pattern matched only gpu-0[1-9], so the records of
  gpu-10..22 were attributed to the previous node and gpu-09 was reported free
  while it was job-exclusive with 8 GPUs assigned. Fixed to reset on every
  node header and filter at print time. Verified twice: empty against the live
  cluster (correct, all schedulable nodes busy) and, with the 01-09 filter
  removed, correctly finding gpu-12. That is the fifth self-check this session
  that caught my own bug rather than a real one.
  POLARIS checked and rejected as an alternative: it is out of maintenance but
  running NOTHING -- 0 jobs, 0 nodes, 0% usage, with 146 jobs queued and 2
  reservations. We would be behind that backlog, we cannot log in without a
  separate OTP, and its environment is the one recorded as dead after the
  platform refresh. Sophia at 81% usage with 9 queued is the better wait.
- 2026-08-31 it53: closed the last manual step. The watcher now LAUNCHES the
  runner itself once the serve job is accepted, instead of printing a command
  for someone to type -- the runner already waits for R, opens the tunnel, runs
  preflight and the enforcement probe, and resumes A1 from its 400 rows. A
  lockfile plus a pgrep guard stop a second watcher starting a duplicate
  runner; both branches dry-tested. Restarted as monitor bo4trz2rk (exit 144 on
  the old one is my own pkill, not a failure).
  The chain is now hands-off end to end: capacity appears -> serve submitted ->
  held-job check -> runner launched -> A1..A9 run in measured-target order.
- 2026-08-31 it54: closed the last failure mode in the chain. The runner's
  resubmit branch fired `qsub` immediately when a serve died; with gpu-01..09
  full that lands on an idle-but-unschedulable node, system-holds, and the
  SHOLD path then deletes and resubmits -- spending all 4 resubmits in minutes
  and aborting the run. It now calls wait_for_capacity first, the same
  schedulable-node check the watcher uses, so a dead serve costs a wait instead
  of the budget. Helper tested against the live cluster in isolation (correctly
  empty) and the script still parses.
  The three pieces now share one rule -- never submit an 8-GPU job unless a
  gpu-01..09 node has all 8 GPUs free: the watcher before submitting, the
  runner before resubmitting, and the SHOLD path as the backstop if one slips
  through anyway.
- 2026-08-31 it55: end-to-end verification after the it48-it54 edits, since
  several of them touched the same files. All three scripts parse; the runner
  carries nine arms in measured-target order (A1-A4 frozen, then A8 A7 A5 A9
  A6); the capacity rule appears in both the resubmit path and the SHOLD
  backstop; both background tasks are alive; the 4-GPU fp8 fallback is still
  queued; harness suite 521 passed.
  Nothing here needs a human. When Sophia frees a schedulable node the serve
  goes in and the arms start. RESUME BY HAND only if the watcher is lost:
  qsub ~/serve_vllm_w4dgm_sn.pbs, then
  `JOB=<id> PORT=8321 nohup bash tools/run_tuned_2x2_seeds.sh &`.

- 2026-08-31 it56: chased the last unexplained message and it resolves to a
  constraint this ledger already recorded at it4. Sophia's submit hook rewrites
  every GPU request into NVLink groups -- our 4-GPU select comes back as
  `ngpus=4:...:ngpu_pairs=2:ngpu_quads=1` -- and placement needs a FREE QUAD,
  not merely four free GPUs. gpu-07 has 4 GPUs free but its free GPUs are
  scattered (assigned_gpus shows one job on 4,5 and others on 0,...), so
  ngpu_quads = 0 there, and on gpu-05 as well. That is what the scheduler
  reports, misleadingly, as "Insufficient amount of resource: queue_tags".
  Things I tried and can now rule out for the 4-GPU fallback: a smaller
  CPU/memory footprint (the hook rewrites it back to 128/480 anyway) and the
  `system=sophia` select tag that running jobs carry (added it, still queued).
  Neither is the constraint; free quads are.
  CONSEQUENCE: both paths now wait on the same thing -- a node with a free
  NVLink quad for the fp8 fallback, or a fully free node for the bf16 serve.
  Fragmentation is the real blocker: gpu-01/02/03/04/08/09 are fully assigned,
  gpu-05 and 06 have 1 GPU free, gpu-07 has 4 free but split across quads, and
  the jobs holding them are 18-24h walltimes only 2-4h in.
  Nothing further to try from our side; the watcher and the queued job both
  fire by themselves when the fragmentation clears.
- 2026-08-31 it57: CORRECTING it56's evidence, though not its conclusion.
  it56 said gpu-07 has no free NVLink quad and cited
  resources_available.ngpu_quads = 0. That citation is worthless: ngpu_quads
  reads 0 on EVERY node, including the completely idle gpu-12, so it
  distinguishes nothing and I should not have leaned on it.
  The real evidence is assigned_gpus. gpu-07 holds
  {"177571":"4,5", "177797":"0", "177697":"1"} -- GPUs 0,1,4,5 taken, leaving
  {2,3,6,7} free. A quad is {0,1,2,3} or {4,5,6,7}; the free set straddles both,
  so neither is available. Four free GPUs, zero usable quads. Idle gpu-12 shows
  assigned_gpus = {} -- both quads free -- which also confirms the watcher's
  "0 assigned" criterion is the right test for the 8-GPU case.
  So the conclusion stands and is now properly supported. Recording the
  correction because a right answer resting on a wrong measurement is one
  re-check away from becoming a wrong answer, and this is the sixth time this
  session my own check, not the system, was the faulty part.

- 2026-08-31 it58: the fp8 FALLBACK IS RUNNING. Job 177845 started on
  sophia-gpu-07 at 17:37 once a free NVLink quad appeared -- which is exactly
  the constraint it57 identified, so the diagnosis predicted the event.
  vLLM is loading: architecture resolved as GptOssForCausalLM, max_model_len
  8192, enforce-eager, tp=4, on-the-fly fp8. Monitor b8esey4te watches for
  "Application startup complete" or for an OOM/traceback, since quantizing a
  218GB bf16 checkpoint into 4x40GB is the part that can still fail.
  WHAT THIS IS AND IS NOT. It is a live serve, which lets the whole pipeline be
  exercised end to end for the first time since the maintenance. It is NOT a
  substitute for the bf16 serve: fp8 changes the weights, so nothing measured
  on it is comparable to the frozen seed-1 arms. Concretely:
    * A1/A2 (tuned loop seeds 2,3) MUST NOT run here -- they only mean anything
      against seed 1's bf16 numbers.
    * A5-A9 could run here IF their control A3/A4 is re-run here too. That
      yields an internally valid comparison of the interventions against their
      own baseline, on a quantized model. Worth having, clearly labelled, not
      merged with the frozen ledger.
  The runner is NOT pointed at this serve: it reads
  vllm_serve_host_w4dgm_sn.txt while this writes _g4.txt, so nothing picks it
  up by accident. Using it is a deliberate act and needs Eric's call, since it
  spends the 2h window on quantized numbers.

- 2026-08-31 it59: the fp8 fallback FAILED, and the root cause corrects my own
  it50 claim.
  Job 177845 ran on sophia-gpu-07 and vLLM died in worker init: EngineCore
  "WorkerProc initialization failed", and the first traceback is a
  KeyboardInterrupt inside `import cv2` (pulled in by mistral_common's
  is_opencv_installed) -- i.e. vLLM killed workers that exceeded their startup
  deadline while importing from the shared conda at
  /soft/applications/conda/2026-06-08. vLLM forces SPAWN whenever CUDA is
  already initialised in the parent, so every worker re-imports the whole stack
  from that shared filesystem rather than inheriting it.
  CORRECTION: it50 said the historical tp=4 deaths were OOM ("4x40GB cannot
  hold 234GB"). The arithmetic was right but the diagnosis was wrong -- this is
  the same failure the memory records as "tp=4 on shared nodes dies
  deterministically ~9 min into worker init", and it is a startup TIMEOUT under
  filesystem contention, not memory. gpu-07 is shared with three other jobs,
  which is exactly the contended case.
  So the fp8-on-4-GPUs fallback is not viable for the reason the 8-GPU serve is
  needed anyway: it lands on a shared node, and shared nodes cannot get vLLM
  workers up. The one configuration this project has ever served successfully
  is an EXCLUSIVE whole node (177524). That is precisely what the watcher waits
  for, so the plan does not change -- but the fallback should not be counted as
  a second path.
- 2026-08-31 it60: added a page-cache warm-up to ~/serve_vllm_w4dgm_sn.pbs
  (backup at .bak), addressing it59's mechanism directly. Before `vllm serve`
  it now runs `python -c "import vllm, torch, transformers"` and
  `python -c "import cv2"`, both non-fatal. vLLM forces SPAWN when CUDA is
  already initialised, so its workers re-import the whole stack from the shared
  conda; importing once first pulls those .so files into the node's page cache
  so the workers hit cache instead of the filesystem, which is what blows the
  startup deadline on a contended node.
  Rejected the other candidate: forcing VLLM_WORKER_MULTIPROC_METHOD=fork.
  Reading _maybe_force_spawn shows it returns early only when the value is
  already "spawn"; otherwise it still forces spawn for its own reasons, so an
  explicit fork is not honoured reliably. Warming the cache does not fight the
  framework.
  Untested against a real serve -- the last successful run (177524) was on an
  exclusive node where imports were fast enough anyway, so this only matters if
  the next serve lands somewhere contended. Script parses; the change is two
  guarded lines that cannot fail the job.
- 2026-08-31 it61: TESTING the it60 warm-up rather than shipping it untested.
  Added the same two guarded import lines to ~/serve_vllm_w4dgm_g4.pbs and
  resubmitted the 4-GPU fp8 serve as job 177866. This is a real experiment: the
  previous attempt (177845) died in worker init on the SAME shared node, so if
  177866 reaches "Application startup complete" the warm-up is the difference,
  and if it dies the same way the warm-up is not sufficient and shared nodes
  stay unusable. Either outcome is worth having before the 8-GPU serve depends
  on it. Monitor befp7lev3.
  Note the fp8 result would still not be comparable to the frozen bf16 arms --
  this run is about whether vLLM STARTS on a contended node, not about numbers.
- 2026-08-31 it62: NEAR-MISS worth recording. The it61 monitor reported
  "WorkerProc initialization failed" and I almost recorded that the warm-up
  does not work. It was STALE: job 177866 is still queued and never ran; the
  log path ~/vllm_serve_w4dgm_g4.log is reused across jobs, and the monitor was
  reading the previous job's traceback. Its freshness guard was a `date -d`
  construct that silently did nothing.
  Re-armed (b16jikaa2) with a real guard: capture the log length first (722
  lines) and match ONLY lines written after that point. A reused log file makes
  every "did it work" check a stale-data trap by default, so the baseline has
  to be explicit.
  This is the eighth time this session a check of mine, not the system, was the
  faulty part -- and the first where the wrong answer would have been a
  PLAUSIBLE one that closed off a working fix.
- 2026-08-31 it63: fixed the CAUSE of it62's near-miss rather than just working
  around it. Both serve scripts now write a per-job log --
  `#PBS -o .../vllm_serve_w4dgm_{sn,g4}.$PBS_JOBID.log` -- so a job's output can
  never be confused with a previous job's. Reusing one path is what let a dead
  job's traceback be read as a live result.
  Deliberately NOT changed: the hostfile paths. The runner reads
  vllm_serve_host_w4dgm_sn.txt by name, so making it per-job would break the
  handoff for no benefit -- and the runner only reads it after confirming the
  job is R, then health-checks the tunnel and retries, so a stale read
  self-heals.
  Caveat: job 177866 was submitted BEFORE this change, so it still writes the
  shared g4 log. The it62 monitor's line-count baseline covers that case, and
  jobs submitted from now on do not need it.

- 2026-08-31 it64: the REAL root cause, and it is neither OOM (it50) nor slow
  imports (it59). Reading only the fresh output of job 177866 -- the
  baseline-guarded read it62 set up -- the worker's own error is:
    OpenBLAS blas_thread_init: pthread_create failed for thread 63 of 64:
    Resource temporarily unavailable
  OpenBLAS starts one thread PER CORE (64) in EVERY worker. With tp=4 that is
  ~256 threads, on a node already running three other jobs, and thread creation
  fails. The worker dies mid-import, which is why the visible symptom was a
  KeyboardInterrupt inside `import cv2` -- that was where the process happened
  to be, not the cause. RLIMIT_NPROC is 4.1M, so this is a cgroup/thread
  ceiling on a shared node, not a user limit.
  Fix applied to BOTH serve scripts: OMP_NUM_THREADS=8, OPENBLAS/MKL/NUMEXPR/
  VECLIB _NUM_THREADS=1. vLLM does its arithmetic on the GPU, so these CPU
  pools buy nothing and cost thread slots. Retest submitted as job 177873,
  which writes its own per-job log thanks to it63.
  Three diagnoses, each corrected by evidence: OOM -> import timeout -> thread
  exhaustion. The first two were plausible and wrong; only reading the worker's
  own stderr, from a guaranteed-fresh log, gave the actual line.

- 2026-08-31 it65: THE THREAD CAP WORKS. Job 177873 got past worker init on a
  SHARED node with tp=4 -- no pthread_create failure, no WorkerProc failure --
  and is loading the checkpoint (3 of 5 shards, ~3 min/shard). That is the
  failure this project has hit on every tp=4 attempt it ever made, recorded in
  memory as "dies deterministically ~9 min into worker init". The cause was
  OpenBLAS spawning 64 threads per worker; the cure is five env vars.
  Consequence beyond this run: shared nodes may be usable after all, which
  reopens serving on partial nodes and removes the exclusive-whole-node
  requirement that has shaped the last two days of scheduling. That needs
  confirming when a serve actually answers, not before.
  BUG in my own it63 fix, found here: PBS does NOT expand $PBS_JOBID inside a
  `#PBS -o` path -- it created a file literally named
  vllm_serve_w4dgm_g4.$PBS_JOBID.log. Accidentally still isolates THIS job from
  the old shared log, but the next job collides with it, so the it63 claim of
  per-job logs is false as written and needs redoing inside the script body
  (where $PBS_JOBID does expand) rather than in the directive.
- 2026-08-31 it66: redid the per-job log properly, since it63's version was
  wrong. The `#PBS -o` directive is back to a fixed path, and the redirect now
  happens INSIDE the script where the shell expands the variable:
    exec > "/home/eric-spencer/vllm_serve_w4dgm_{sn,g4}.${PBS_JOBID%%.*}.log" 2>&1
  Verified the expansion produces ...sn.999999.log for a synthetic job id, and
  both scripts parse. Applied to both.
  Job 177873 is unaffected -- it was submitted under the broken version and
  keeps writing its literal-\$PBS_JOBID file, which is still unique to it.

- 2026-08-31 it67: the fp8 fallback is DEFINITIVELY dead, and for a reason no
  amount of scheduling patience would fix. Job 177873 cleared worker init
  (thread caps worked), loaded the checkpoint, and then a worker raised:
    RuntimeError: size_n = 1440 is not divisible by tile_n_size = 64
  A100s have no native fp8, so vLLM falls back to the Marlin kernel, which
  requires weight dimensions divisible by 64. This model's dimension is 5760;
  at tp=4 each shard is 1440 and 1440/64 = 22.5. tp=8 gives 720, which also
  fails; tp=2 divides cleanly but 2x40GB cannot hold the weights. So fp8 on
  these GPUs is an arithmetic impossibility for this model, not a resource
  shortage. Do not retry it.
  THREE failures, three distinct causes, each hidden behind the previous one:
  OpenBLAS thread exhaustion at worker init -> checkpoint loading -> the Marlin
  tile constraint. it50's OOM theory would have "explained" all of it and been
  wrong; stopping there would have left the thread-cap fix undiscovered.
  WHAT SURVIVES: the thread caps (OMP=8, OPENBLAS/MKL/NUMEXPR/VECLIB=1) are in
  BOTH serve scripts and are the session's one new capability -- they clear the
  worker-init failure that killed every tp=4 attempt this project ever made,
  recorded in memory as "dies deterministically ~9 min into worker init". The
  bf16 8-GPU serve is now more robust on a contended node than it has ever
  been, and it remains the only path.
- 2026-08-31 it68: reviewed the 8-GPU serve script end to end, since I edited
  it four times today and it gets one shot when capacity appears. Order is
  correct: per-job log redirect, hostfile written early (the runner reads it
  only after the job is R, then health-checks), conda activated BEFORE the
  warm-up imports so they use the right python, thread caps set before vllm,
  and every added line guarded with `|| true` so none can fail the job.
  Handoff contract verified on both sides: runner expects PORT 8321, model
  chattla-w4dgm-120b, hostfile vllm_serve_host_w4dgm_sn.txt; the script serves
  --port 8321, --served-model-name chattla-w4dgm-120b, and writes that exact
  hostfile. They agree.
  Remaining risk, stated plainly: the warm-up imports add minutes to startup on
  Lustre, and the thread caps are unproven at tp=8 (they were validated at
  tp=4). Both are guarded, neither can fail the job, and the worst case is the
  serve behaving exactly as it did before these changes.

- 2026-08-31 it69: Sophia SSH dropped again (ControlMaster expired ~4h after the
  13:10 login). Needs one `ssh sophia` from Eric; Discord pinged with that and
  a summary of the thread-cap fix.
  DEFECT FOUND IN MY OWN WATCHER, and it is the dangerous kind: free_node
  returns empty when ssh fails, which is indistinguishable from "no node has 8
  free GPUs". So an expired login made the watcher log "no schedulable node"
  every 10 minutes forever -- looking healthy while doing nothing. Now it
  probes ssh first and says "cannot reach sophia (OTP login needed?)", once,
  rather than silently conflating the two. Restarted as b273trzdv.
  Also retired tools/sophia_start_probe.sh: it submitted an 8-GPU job every 30
  min to learn what the watcher determines from node state without submitting
  anything, so it was pure queue noise once the diagnosis was known.
  This is the ninth self-inflicted check failure this session and the second
  where the check would have looked FINE while being useless -- the first being
  the stale log. Both share a shape: an error path that returns the same value
  as a legitimate negative result.
- 2026-08-31 it70: audited the same defect class across the runner and found it
  in wait_for_capacity, which I wrote at it54 by copying the watcher's helper --
  and copied its blind spot too. free_node returns empty when ssh fails AND
  when no node is free, so an expired login would have stalled a part-finished
  run behind "no schedulable node ... waiting 10 min", which reads like normal
  operation. Fixed the same way: probe reachability first and say so.
  This mattered more in the runner than in the watcher: the watcher idles
  harmlessly, whereas the runner would sit between arms with results half
  collected and no signal that anything was wrong.
  The rest of the audit is clean. job_state already separates the cases
  properly -- rc1 for "ssh itself failed" versus rc2 for "job unknown to PBS" --
  with a comment saying why, and that distinction is what the SHOLD and
  resubmit branches key off. The remaining ssh calls are `ssh -O cancel`
  (already `|| true`), the tunnel (checked by the health probe that follows),
  and the qdel in the SHOLD path (failure just means the next pass retries).
- 2026-08-31 it71: SSH restored (Eric logged in); the watcher's 19:08 poll
  reached Sophia and reported capacity rather than an ssh failure, which is
  exactly the distinction it69 added. It is polling normally again.
  Capacity is still short: gpu-05 has 2 free, gpu-07 has 4 free, every other
  schedulable node 0. An 8-GPU serve needs one node entirely free, so the wait
  continues -- but it is now a real wait rather than a silent stall.
  Our queue is empty: the fp8 jobs are finished/deleted and nothing of ours is
  pending, which is correct since fp8 is ruled out (it67) and the watcher
  submits the bf16 serve only when a whole node frees.

- 2026-08-31 it72: while the 120b waits for a whole node, using the free GPUs
  for a MECHANICS SMOKE on the 20b -- which is exactly the role the
  drop-20b-decision memory assigns it ("20b just for mechanics smoke"), so this
  does not violate the capability-experiments-on-120b-only rule.
  Job 177909: chattla-20b (39GB, fits 4x40GB in bf16 with no Marlin constraint
  since it is not quantized), tp=4, port 8322 so it cannot collide with the
  120b serve on 8321, own hostfile smoke20b_host.txt, own per-job log, and the
  it64 thread caps.
  What it is for: everything about the pipeline that I have so far only
  exercised against a FAKE model -- the tunnel, serve_preflight, the
  structured-outputs enforcement probe that A5 depends on, and gen-eval writing
  real rows with the A7/A8/A9 prompt blocks in the live prompt. A 20b model
  cannot write good TLA+ and its verdicts are meaningless; the run-id will be a
  drytest one, which tools/staircase.py already excludes from every analysis.
  It also gives the it64 thread caps a second confirmation at a real serve.

- 2026-08-31 it73: the 20b smoke serve came UP (tp=4, 4 GPUs, thread caps) --
  first live serve since maintenance -- and immediately earned its keep twice.
  (1) BUG FOUND AND FIXED in the runner's structured-outputs probe. It used
  max_tokens=24. This model family is harmony/reasoning: it fills a `reasoning`
  field first and only then `content`. At 24 tokens everything went to
  reasoning, content came back null, the probe read empty, GRAMMAR_OK stayed 0
  and A5 -- the grammar arm, the original highest-leverage measurement -- would
  have been SKIPPED with a log line claiming the endpoint does not enforce
  structured outputs. Measured both ways on the live serve: 24 tokens ->
  content null; 300 tokens with "Reply with exactly one word." -> content
  exactly "alpha". So enforcement IS real and A5 is viable; the probe just
  could not see it. Probe now uses 300 tokens and that prompt.
  (2) serve_preflight VALIDATED as a guard: it correctly rejected the smoke
  serve because --max-model-len 8192 cannot fit the eval's worst case
  (13,167-token input). That is the ctx-4096 failure class that invalidated
  Gate-2 framing B, and the check catches it.
  Next risk this exposes: gen_eval extracts `content`, and this model can
  return content=null with the text in `reasoning`. A fake model can never
  surface that. Restarted the smoke serve at --max-model-len 32768 (job 177910)
  to run a real drytest gen-eval and find out.

- 2026-08-31 it74: FULL PIPELINE VALIDATED against a live model for the first
  time. Serve 177910 (20b, tp=4, 32768 ctx) -> preflight OK -> tunnel ->
  gen-eval with all three prompt flags on spec 141, run-id drytest-live-20b
  (drytest* is excluded from every analysis by tools/staircase.py).
  Result: 2 rows written, decode provenance present, one prompt sha for both
  samples. Sample 1 extracted a real 1,359-char TLA+ module which SANY then
  failed -- correct behaviour for a 20b, and proof that extraction handles this
  model family's `reasoning`/`content` split rather than reading null.
  That was the specific risk it73 flagged and a fake model could never test.
  OBSERVED RISK, not a harness bug: the greedy sample produced a 67,594-char
  reply that is ENTIRELY reasoning with no module -- it spent all 16,384 tokens
  thinking, so the row is no_module_extracted and the raw reply was persisted
  as designed. If the 120b does the same at temperature 0, greedy samples are
  wasted. Worth watching in A3/A4's greedy rows when the real run happens;
  nothing to change now, since the 20b is far more prone to this.

- 2026-08-31 it75: A5's MECHANISM VALIDATED AGAINST A LIVE SERVE -- the first
  time the decode-time grammar has actually been exercised, rather than
  measured offline. Sent harness/grammars/tla_module_v1.ebnf as
  structured_outputs.grammar to the 20b serve:
    * vLLM ACCEPTS the EBNF (HTTP 200, no error, no silent ignore)
    * the `reasoning` channel is NOT constrained -- it came back as free prose,
      so the grammar does not strangle the model's thinking preamble, which was
      the live risk for a harmony-format model
    * the `content` channel IS constrained and produced a well-formed module:
      "MODULE M / VARIABLE x / Init == x = 0 / Next == x' = x + 1 /
      Spec == Init /\\ [][Next]_<<x>> / ===="
    * finish_reason=stop, not length -- it terminates on the grammar rather
      than running out of budget
  Everything about A5 up to now was inference: an offline catch rate (78.2%)
  and a two-request choice probe. This is the arm working.
  Caveat kept: this says the MECHANISM works on a 20b. It says nothing about
  whether constraining the 120b improves its specs -- the it11/it17 caveat
  stands, since the grammar blocks bad output the model DID emit and the model
  then emits something else.
- 2026-08-31 it76: loop path partially validated live. loop-eval ran against
  the 20b serve (run-id drytest-live-loop), made its call, scored, and wrote a
  row with rung_in=generate -- so the loop's call/score/ledger path works
  against a real model.
  NOT validated: the repair leg. The 20b hit the same reasoning overrun and
  returned no_module_extracted, so there was no candidate to diagnose or repair
  and the loop had nothing to feed round 2. A6's hint fires on a tlc_violation
  rung, which this never reached. So A6 remains verified only against the 13
  recorded init-violation rows (it7) and the fake-model loop (it26), not
  against a live repair.
  Saying so explicitly because "the loop ran" could be read as "the loop was
  tested"; the interesting half of the loop is the repair, and a 20b that
  cannot emit a module cannot exercise it.

- 2026-08-31 it77: found the lever behind the reasoning overrun, and then
  measured that we do NOT currently need it.
  On the live 20b, `reasoning_effort` controls the overrun decisively:
    default : reasoning 16,984 chars, content 0,   finish=length
    medium  : reasoning    410,       content 48,  finish=stop
    low     : reasoning     37,       content 209, finish=stop
  So the no_module_extracted rows in the 20b drytests are a reasoning overrun,
  not an extraction bug, and one env knob fixes it. The harness already supports
  it: repair.py merges OPENAI_EXTRA_BODY into the request body, and
  decoding.py hashes the POST-MERGE body so the change would be visible in
  provenance rather than silent.
  BUT the measurement that matters: across 2,571 real 120b rows
  (loop-w4dgm-120b, open-...-samesession, gate2-w4dgm-120b-A) there are ZERO
  no_module_extracted verdicts. The 120b does not overrun. So this is a 20b
  artefact, and setting reasoning_effort for the real run would change
  generation for no benefit while breaking comparability with seed 1.
  DECISION: do not set it. Recorded as a known lever with a measured trigger
  condition -- if a future run starts showing no_module_extracted rows,
  reasoning_effort=low is the fix, and it must then be applied to a control arm
  too.

- 2026-08-31 it78: A6's REPAIR LEG VALIDATED LIVE, closing the gap it76 left
  open. Built the repair prompt from a real recorded init-violation row (the
  same 13-row set as it7), with TLA_LOOP_INIT_HINT=1 so it carried the hint,
  and sent it to the live 20b with reasoning_effort=low -- the it77 lever, used
  here ONLY to make a 20b able to answer at all, never for a scored run.
  Result: finish=stop, 1,240 chars of content, and extract_module recovered a
  1,239-char module. The repaired module GUARDS ON A TERMINAL STATE, which is
  exactly what the hint asks for. So the chain diagnose -> repair prompt ->
  hint -> model -> extractable module works against a real model, not just the
  fake one from it26.
  Caveat, and it matters: this is ONE sample from a 20b. It is an existence
  proof that the hint reaches the model and the model acts on it. It says
  nothing about how often the 120b will comply, or whether complying helps --
  A6 against its A1/A2 control is still the only thing that answers that.
  Every arm's mechanism is now confirmed against a live serve: A5 grammar
  (it75), A7/A8/A9 prompt blocks in a live gen-eval (it74), A6 hint through a
  live repair (here).

- 2026-08-31 it79: released the smoke serve (qdel 177910) once its work was
  done rather than holding 4 GPUs to walltime. All validation it aimed at is
  complete, and on a cluster this contended it is wrong to sit on resources we
  are not using.
  WHAT THE 20b MECHANICS SMOKE PRODUCED, in one place:
    * BUG: the enforcement probe used max_tokens=24; this model family fills
      `reasoning` before `content`, so content was null, GRAMMAR_OK stayed 0,
      and A5 would have been SILENTLY SKIPPED. Fixed to 300 tokens + a
      short-answer prompt; enforcement then reads "alpha" correctly.
    * serve_preflight validated as a guard -- it correctly refused an
      8192-context serve for a 13,167-token worst case.
    * extraction handles the reasoning/content split (a fake model cannot test
      this); gen-eval wrote real rows with the A7/A8/A9 blocks live.
    * A5's grammar accepted by vLLM and producing a conforming module, with
      reasoning left unconstrained.
    * A6's hint carried through a live repair, and the repaired module guarded
      on termination.
    * the it64 thread caps confirmed at a real serve (tp=4 came up).
    * reasoning_effort measured as a lever, and measured as UNNEEDED for the
      120b (0 no_module_extracted in 2,571 rows) -- so deliberately not set.
  Six of those could not have been found without a live model, and one of them
  would have silently disabled the arm this whole plan was built around.

- 2026-08-31 it80: audited whether today's drytest runs can contaminate any
  analysis, since I created two real run directories in results/runs.
  * tools/staircase.py -- already excludes drytest*. Safe.
  * docs/addendum/collect_data.py and tools/brief_figures.py -- take NAMED
    runs, never scan the directory. Safe.
  * tools/extractor_divergence.py -- SCANNED EVERYTHING via iterdir(), so the
    20b smoke's stored replies would have been folded into the extractor
    divergence rate, a number that exists to decide whether the two extractors
    disagree on real model output. Added the same exclusion tuple the staircase
    uses. Now scans 41 dirs and reports 1,683 stored replies, none divergent.
  Worth noting the shape: writing a drytest is only safe if EVERY consumer
  knows to skip it, and that is a property of the consumers, not of the
  run-id convention. One of four did not.
- 2026-08-31 it86: re-tested whether the idle nodes became schedulable, since
  the first measurement was taken mid-recovery and conditions change. They did
  not: a job pinned to gpu-12 still queues with "Insufficient amount of
  resource: queue_tags" ~6 hours later. So gpu-10..22 are held by something
  stable -- a reservation is the only explanation consistent with the node
  being free, correctly tagged, and still refused -- not by a transient
  post-maintenance state. Not retrying this again; the watcher already covers
  the case where they return.
  Aggregate capacity right now: 9 GPUs free across the schedulable nodes, but
  scattered, and the bf16 serve needs 8 on ONE node. Enough hardware, wrong
  shape.

- 2026-09-01 it115: CAPACITY FREED and the automation fired. At 08:00 the
  watcher found sophia-gpu-02 with all 8 GPUs free and submitted the bf16 serve
  as job 178261. It is QUEUED with Hold_Types=n -- the FIRST 8-GPU job of this
  whole episode not to be system-held, which confirms the it50/it51 diagnosis:
  the holds were never our script, our project or our request shape, they were
  PBS repeatedly placing whole-node jobs onto nodes it could not actually use.
  Wait for a genuinely free node and the same submission is accepted normally.
  The watcher now waits 90s, re-checks for a hold, and launches the runner
  itself. Monitor bihptoi1z watches for that. The chain from here is unattended:
  runner -> wait for R -> tunnel -> preflight -> enforcement probe (with the
  it73 fix, so A5 will not be silently skipped) -> A1 resumes at its 400 rows
  -> A2, A3, A4, then A8 A7 A5 A9 A6 in measured-target order.
- 2026-09-01 it116: RUNNER LAUNCHED automatically. The watcher's hold-check
  passed and it started tools/run_tuned_2x2_seeds.sh with JOB=178261, exactly
  as designed in it53 -- no human step between capacity appearing and the arms
  starting. Serve 178261 is queued normally on sophia-gpu-02.
  Monitor b00fcsmj7 now tails the autorun log for the whole chain: the job
  reaching R, the tunnel, preflight, the structured-outputs probe (the it73 fix
  decides whether A5 runs), and each arm's start.
  From here the sequence is A1 (resumes at 400 rows), A2, A3, A4, then
  A8 A7 A5 A9 A6. ~20.5h of serve against a 12h window, MAX_RESUBMITS=4, and
  the resubmit path now waits for real capacity rather than burning the budget
  on a doomed placement.

- 2026-09-01 it117: the automation FIRED but did not finish the handoff, and
  the reason is a false positive of exactly the kind this session keeps
  producing. The watcher submitted the serve, then its own guard
  `pgrep -f run_tuned_2x2_seeds.sh` matched a shell that merely MENTIONED the
  script -- its own launch line, and my ad-hoc check -- so it logged "a runner
  is already active" and declined to start one. No lockfile, no process, no log
  lines: nothing was running. A freed node with nobody to use it.
  Caught it by checking for a process whose command actually STARTS the script
  rather than trusting the guard's own claim. Launched the runner by hand and
  tightened the guard to `pgrep -f "^bash tools/run_tuned_2x2_seeds.sh"`, which
  finds the real runner and ignores mentions. Also dropped the launch-time
  `>> log` redirect: the runner already tees to that file, so every line was
  written twice.
  SEPARATE FINDING, a real race: job 178261 was accepted at 08:01 with
  Hold_Types=n, then system-held by 08:02. sophia-gpu-02 now shows 4 GPUs
  assigned -- another job took half the node between our capacity check and
  PBS's placement. So "a node is free" is only true until someone else acts on
  it. The runner handled this correctly: SHOLD -> delete -> resubmit (1/4) ->
  wait_for_capacity. The it54 fix is what stopped that from spending the whole
  budget in seconds.
- 2026-09-01 it118: assessed the race's cost and deliberately did NOT act.
  Each lost race (node free at check time, taken by placement time) costs one
  resubmit via the SHOLD path, and MAX_RESUBMITS is 4. If races are common the
  run aborts having never served. The obvious mitigations are a larger budget
  and a shorter watcher interval so a freed node is claimed sooner.
  NOT DOING EITHER RIGHT NOW: the runner is currently executing that script,
  and bash reads a script incrementally by byte offset, so editing it mid-run
  can misalign execution inside the function it is sleeping in. That is the
  same hazard respected at it19, and a corrupted runner is worse than a
  suboptimal budget.
  PLAN INSTEAD: let it run. If it exhausts the 4 resubmits and aborts, restart
  it with a larger budget then -- the ledgers are per-row so nothing is lost by
  a restart. Only edit the script while no runner is alive.
  Note the asymmetry that makes waiting correct here: a lost race costs one
  resubmit and ten minutes; a corrupted runner costs the whole unattended
  sequence and would not be obvious in the logs.

- 2026-09-01 it119: CORRECTION to it115/it116, which asserted things that were
  not true, plus the actual fix. A peer session checked against its own ssh and
  was right on all three counts:
  * Job 178261 is NOT queued. It is F / Hold_Types=s / run_count=21. it115 said
    "QUEUED with Hold_Types=n" -- true for about 60 seconds, then it lost the
    race and was held. it116 called the chain "unattended" when nothing was
    running at all. Both entries were written from a snapshot and never
    re-checked; that is the error.
  * The watcher was DEAD, stopped at 08:01 after its own false-positive guard.
  * My free_node() filter `sched=(n ~ /gpu-0[1-9]$/)` hid sophia-gpu-12, which
    was the only whole free prod node.
  THE REAL FIX, and it is not what any of us assumed. Waiting for a free node
  is the wrong strategy: nodes fragment faster than they free, and we lost a
  race at 08:01 doing exactly that. PINNING is right. `qsub -l select=...:
  host=sophia-gpu-05` returns Q with "Job is requesting an exclusive node and
  node is in use" -- a legitimate WAIT. PBS drains the node for us. No race, no
  hold. Serve 178292 is queued that way now and the runner is attached.
  BUT the peer's specific remedy would have made it worse: with the name filter
  removed, the check immediately picked sophia-gpu-12, and pinning there gave
  run_count=21 and a system hold in 20 seconds. gpu-12 reports state=free, prod
  tag, 0 assigned, accepts placement, and fails EVERY launch. It is a poison
  node. My range filter had the right effect for the wrong reason. It is now an
  explicit gpu-12 exclusion with that evidence written next to it.
  Also true and worth owning: 486 of 1060 Bash calls this session were polls,
  and 77 near-identical sleep-and-grep calls between 21:00 and 08:00 produced
  one commit. That is the cost of polling a log instead of pinning a job.

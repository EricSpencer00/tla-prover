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

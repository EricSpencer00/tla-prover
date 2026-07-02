# DRAFT_ITERATION.md — Stage-0 draft-config iteration

Scope: the 60 corpus specs whose TLC config is a draft (`corpus/configs/drafts/*.cfg`,
no original cfg in `tla_benchmark/data/cfg/`). Baseline = `results/runs/oracle-v1`;
final state = `results/runs/draftfix-final` (same command, fresh run-id). Intermediate
runs: `draftfix-1`, `draftfix-2`, `draftfix-3`.

Reproduce:
`cd /Users/eric/GitHub/prove-TLA && python3 -m harness run --run-id draftfix-final --specs <60-list> --timeout 120 --jobs 6 --extra-cfg-dir corpus/configs/drafts`

## Headline

| status                     | oracle-v1 | draftfix-final |
|----------------------------|-----------|----------------|
| sany=pass, tlc=pass, clean | 9         | **20**         |
| pass but vacuous           | 14        | 17             |
| error / fail / timeout     | 37        | 23             |

New file: `corpus/configs/policy.json` (9 specs get `-deadlock`, each with a
termination-by-design justification). Upstream ground truth consulted throughout:
local clone `/Users/eric/GitHub/tla-examples` (tlaplus/examples).

## Per-spec disposition

Population labels: `state_machine` | `mc_wrapper` (an MC model-checking module) |
`proof_module` (TLAPS proofs; per PLAN Amendment 1 their G1 criterion is TLAPS, not TLC) |
`library` (operator/theorem/component module — TLC pass undefined).

### Now clean (sany=pass, tlc=pass, vacuity=clean) — 20

| spec | module | population | change made |
|------|--------|------------|-------------|
| 2   | ACP_NB | state_machine | policy `-deadlock` (commit/abort termination by design) |
| 5   | ACP_SB | state_machine | policy `-deadlock` (same) |
| 38  | (unchanged) | state_machine | already clean |
| 45  | (unchanged) | state_machine | already clean |
| 62  | EWD687aPlusCal | state_machine | cfg: `none = none` model-value override for unbounded CHOOSE; policy `-deadlock` (upstream MCEWD687a.cfg sets CHECK_DEADLOCK FALSE) |
| 67  | EWD840_proof | proof_module (also TLC-clean) | policy `-deadlock` (termination detection quiesces) |
| 102 | KeyValueStore | state_machine | already clean |
| 104 | MCKVS | mc_wrapper | already clean |
| 112 | LamportMutex_proofs | proof_module (also TLC-clean) | cfg: `Clock = {1,2,3,4}` definition override (Clock == Nat \ {0} non-enumerable; module comment prescribes 1..maxClock+1) + `CONSTRAINT ClockConstraint` |
| 121 | LeastCircularSubstring | state_machine | cfg: `Nat <- [ZSequences]CharacterSet` module-scoped override — the only in-scope finite Nat-subset; bounds string length to <= 2 (upstream uses [ZSequences]ZSeqNat from the MC wrapper) |
| 122 | MCLeastCircularSubstring | mc_wrapper | cfg: added `Nat <- [ZSequences]ZSeqNat` per upstream MCLeastCircularSubstringSmall.cfg |
| 144 | Elevator | state_machine | already clean |
| 147 | MCNano | mc_wrapper | cfg: added `NoHash = [Nano]NoHashVal`, `NoBlock = [Nano]NoBlockVal`, `VIEW View` per upstream MCNanoSmall.cfg (Nano's NoHash/NoBlock are unbounded CHOOSEs) |
| 151 | Queens | state_machine | policy `-deadlock` (solver terminates, Termination property in spec) |
| 152, 165, 172 | (unchanged) | state_machine | already clean |
| 174 | Slush | state_machine | cfg rewritten to upstream SlushSmall.cfg: `NoColor = NoColor`, `NoMessage = NoMessage` model-value overrides (were the unbounded CHOOSEs), 3 nodes, SampleSetSize/PickFlipThreshold = 2 |
| 179 | SpanTreeTest | state_machine | policy `-deadlock` (spanning-tree computation converges) |
| 191 | Hanoi | state_machine | already clean |

### Pass but vacuous (no invariant possible from cfg) — 17

* **Libraries (14)** — no VARIABLES, nothing to model-check; cfg stays a stub;
  per Amendment 1 their G1 criterion is SANY (+ TLAPS on any proved theorems):
  29 CarTalkPuzzle (also: shrank N/P from 100/45 to 10/4 — the old values burned the
  full 120 s timeout during TLC startup; now completes instantly),
  56 Relation, 105 DyadicRationals, 110 Functions, 114 NaturalsInduction,
  115 SequenceTheorems, 117 WellFoundedInduction, 123 ZSequences, 190 Bits,
  and the five duplicate copies of TLAPS.tla: **69, 86, 116, 183, 200** (corpus
  defect already on record).
* **182 sums_even** — proof_module (theorems only). TLAPS is its criterion.
* **108 Prob** — state_machine. policy `-deadlock` (absorbing Markov chain; state space
  is finite because Norm(p)=0 disables Next once den > 100000). No zero-arity predicate
  exists to cite as INVARIANT, and its THEOREM name (`Converges`) is not a definition —
  TLC rejects `PROPERTY Converges` ("not defined in the specification"; verified in
  draftfix-1). **Flagged for MC wrapper** adding a TypeOK.
* **145 MultiPaxos (MultiPaxos-SMR)** — state_machine. Removed the drafted
  `PROPERTIES Termination`: Spec has no fairness conjunct, so the liveness "violation"
  in oracle-v1 was a drafting error, not an algorithm bug. The module defines no safety
  predicate; TypeOK/Linearizability live in MultiPaxos_MC (**spec 146, original cfg**),
  the canonical model. Shrank to Writes={w1}, MaxBallot=2 (assumption requires >= 2).

### Still failing, with cause and coverage — 23

| spec | module | population | verdict |
|------|--------|------------|---------|
| 30  | cbc_max | state_machine | **CORPUS FINDING.** With `-deadlock` TLC reaches a real evaluation failure: `MAX(V[i])`'s CHOOSE has no witness when a process enters PHS1 after buffering >= N-T Phs1 messages while still in BCAST1 (V[i] still all Bottom). TLC also warns that action Recv assigns `V'` while listing `V` in its UNCHANGED tuple (line 78) — a genuine spec defect. Left failing per instructions. |
| 39  | Age_Channel | library (component) | No zero-arity Next (parameterized actions only). Instantiated by EnvironmentController (**spec 40, original, clean**). |
| 41  | EPFailureDetector | library (component) | Same; covered by spec 40. |
| 47  | DiskSynod | state_machine | Operator constants `Ballot(_)`, `IsMajority(_)`; no in-module operator to substitute via `<-`. Needs MC wrapper (upstream only ships MC_HDiskSynod). |
| 48  | HDiskSynod | state_machine | Same inherited operator constants; canonical model is MC_HDiskSynod (**spec 49, original** — itself currently a 120 s timeout, see findings). |
| 50  | Synod | state_machine | `SynodSpec == \EE chosen, allInput : ...` — TLC cannot check temporal existentials; ISpec lives in inner module. Needs wrapper instantiating Inner with concrete variables. |
| 53  | RingBuffer | library (component) | LOCAL-INSTANCE component of the Disruptor specs; meant to be instantiated. |
| 81  | EWD998_optsSC | library (tooling) | Simulation-control script (CSV/IOExec); ASSUME not TLC-evaluable; upstream drives it from shell scripts. |
| 107 | KnuthYao | state_machine | Deadlock is by design (policy), but s3->s1/s6->s2 loops halve p forever: infinite state space, exhaustive TLC overflows at den=2^31. No in-module constraint predicate. Upstream checks by simulation only (SimKnuthYao). **Flagged for MC wrapper.** |
| 118 | AddTwo | proof_module | x increments forever; no constraint operator defined; `Even`'s definition quantifies over Nat (non-enumerable). TLAPS proof exercise; TLC needs a wrapper. |
| 119 | FindHighest | proof_module | `f \in Seq(Nat)` init; upstream fixes this with **MCFindHighest.tla/.cfg which were never extracted into the corpus** (corpus finding). |
| 124 | LevelSpec | library | Constant-only spec of TLA+ level-checking; Node is a function-valued constant. |
| 131 | MajorityProof | proof_module | Parent draws `seq \in Seq(Value)`; bounding op (BoundedSeq) lives only in MCMajority (**spec 132, original, clean**). |
| 134 | MCReachabilityTest | library (test harness) | ASSUME-driven constant test (`Test` tuple); no behavior spec, so TLC has nothing to run even with `SuccSet <- RandomSuccSet`. Would need a harness constant-evaluation mode. |
| 137 | ParReachProofs | proof_module | Function constant Succ; TLC coverage via MCParReach (**133, original, clean**). |
| 138 | Reachability | library | Constant-only operator module (ReachableFrom). |
| 139 | ReachabilityProofs | proof_module | Pure theorem module over Reachability. |
| 142 | ReachableProofs | proof_module | Function constant Succ; TLC coverage via MCReachable (**135, original, clean**). |
| 148 | Nano | state_machine | Operator/function constants (CalculateHash, KeyPair, Ownership); canonical model is MCNano (**147, now clean**). |
| 176 | spanning | state_machine | `nbrs \subseteq Proc \X Proc` not expressible in cfg; canonical model MC_spanning (**175, original — currently fail_invariant, see findings**). |
| 189 | TLCMC | state_machine | Record-valued StateGraph; upstream checks via TestGraphs.tla/.cfg, **not in corpus** (corpus finding). |
| 192 | HanoiSeq | state_machine | Sequence-valued constants A,B,C; upstream ships no cfg; needs MC wrapper (e.g. A == <<3,2,1>>). |
| 198 | Alternate | library (parameterized) | Operator constants `XInit(_)`, `XAct(_,_,_)`; a template meant to be instantiated. |

## Corpus findings (to route per PLAN Amendment 1 "repair from upstream")

1. **spec 30 (cbc_max)**: Recv assigns `V'` and simultaneously lists `V` in UNCHANGED
   (TLC warning), and `MAX`'s CHOOSE fails on a reachable state (messages buffered
   before entering PHS1). Real spec defect; left failing (`draftfix-final/logs/30.log`).
2. **Missing MC wrappers upstream has**: MCFindHighest (for 119), TestGraphs (for 189) —
   never extracted into the corpus; extracting them is the clean fix.
3. **Five TLAPS.tla duplicates** (69/86/116/183/200) — already-known corpus defect,
   confirmed: population=library, stub cfgs retained.
4. **Original-cfg regressions observed in oracle-v1** (out of this task's scope but
   adjacent): 49 MC_HDiskSynod and 146 MultiPaxos_MC time out at 120 s;
   175 MC_spanning reports fail_invariant. These are the canonical coverage for
   drafted specs 48, 145, 176, so they matter for G1 closure.
5. **Draft cfg for 145** previously checked `Termination` against a fairness-free Spec —
   a guaranteed-false liveness property (drafting error, now removed and documented).

## Out of scope here

11 further specs have draft cfgs but never reach TLC because **SANY fails**
(71, 72, 80, 83, 87, 89, 101, 106, 129 `sany=fail`; 77, 140 `sany=fail_missing_module`).
Those are parse/module-resolution corpus bugs, not cfg problems — separate workstream.

## Remaining blockers, ranked

1. MC wrappers needed (cannot be expressed in cfg syntax): 47/50, 107, 108, 118, 189, 192
   — plus corpus extraction of upstream MCFindHighest and TestGraphs for 119/189.
2. Harness support for constant-only / ASSUME-test modules (29, 124, 134, 138, 140-class)
   if the population-aware criterion wants more than SANY for them.
3. TLAPS runs are the real pass criterion for the proof modules
   (67, 112, 118, 119, 131, 137, 139, 142, 182) — 67 and 112 already TLC-clean as a bonus.

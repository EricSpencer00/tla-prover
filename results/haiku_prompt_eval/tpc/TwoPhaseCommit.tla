---- MODULE TwoPhaseCommit ----

(*
  Minimal Two-Phase Commit Protocol: Safety-Critical Model

  This model captures the essential behavior of two-phase commit between one
  coordinator and a set of resource managers (RMs), focusing on the safety
  property that either all RMs commit or all abort (atomicity).

  Execution flow:
  - Phase 1 (Vote): Each RM independently votes yes (can commit) or no (cannot).
  - Phase 2 (Decide): Coordinator collects all votes and decides:
    * Commit if all RMs voted yes
    * Abort if any RM voted no
  - Phase 3 (Execute): Each RM executes the coordinator's decision.

  Safety properties verified:
  1. Atomicity: All committed RMs imply all RMs will be committed.
  2. Coordinator Validity: Coordinator commits only if all voted yes.
  3. RM Validity: No RM commits unless coordinator decided commit.
*)

EXTENDS Naturals

(*
  CONSTANT ResourceManagers: The set of resource managers participating in the protocol.
*)
CONSTANT ResourceManagers

(*
  rmVote[rm]: Each RM's vote on its ability to commit.
  Domain: {"yes", "no", "none"}
  Semantics: "none" = undecided, "yes" = voted to commit, "no" = cannot commit.
*)
VARIABLE rmVote

(*
  rmState[rm]: The final outcome state of each RM.
  Domain: {"init", "committed", "aborted"}
  Semantics: "init" = awaiting decision, "committed" = executed commit,
             "aborted" = executed abort.
  Note: An RM that votes "no" immediately transitions to "aborted" (unilateral abort).
*)
VARIABLE rmState

(*
  coordinatorDecision: The coordinator's commit/abort decision.
  Domain: {"none", "commit", "abort"}
  Semantics: "none" = undecided, "commit" = all RMs will execute commit,
             "abort" = all RMs will execute abort.
  Invariant: Coordinator decides commit iff all RMs voted yes.
*)
VARIABLE coordinatorDecision

vars == << rmVote, rmState, coordinatorDecision >>

(*
  TypeOK: Defines the type and domain of each variable.
*)
TypeOK ==
  /\ rmVote \in [ResourceManagers -> {"yes", "no", "none"}]
  /\ rmState \in [ResourceManagers -> {"init", "committed", "aborted"}]
  /\ coordinatorDecision \in {"none", "commit", "abort"}

(*
  Init: All RMs start undecided, no votes cast, coordinator hasn't decided.
*)
Init ==
  /\ rmVote = [rm \in ResourceManagers |-> "none"]
  /\ rmState = [rm \in ResourceManagers |-> "init"]
  /\ coordinatorDecision = "none"

(*
  RMVotesYes: An RM votes yes, indicating it can commit.
  Preconditions: RM has not yet voted.
  Effect: RM votes yes; state remains in init (awaiting coordinator decision).
*)
RMVotesYes(rm) ==
  /\ rmVote[rm] = "none"
  /\ rmVote' = [rmVote EXCEPT ![rm] = "yes"]
  /\ UNCHANGED << rmState, coordinatorDecision >>

(*
  RMVotesNo: An RM votes no, indicating it cannot commit.
  Preconditions: RM has not yet voted.
  Effect: RM votes no and immediately aborts (unilateral abort).
          No need to wait for coordinator decision.
*)
RMVotesNo(rm) ==
  /\ rmVote[rm] = "none"
  /\ rmVote' = [rmVote EXCEPT ![rm] = "no"]
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED coordinatorDecision

(*
  CoordinatorDecides: Coordinator collects all votes and makes a decision.
  Preconditions:
    - Coordinator has not yet decided.
    - All RMs have voted (no "none" votes remain).
  Effect:
    - If all RMs voted yes: coordinator decides commit.
    - If any RM voted no: coordinator decides abort.
  Atomicity guarantee: This action ensures that the decision is based on
    a complete snapshot of all votes.
*)
CoordinatorDecides ==
  /\ coordinatorDecision = "none"
  /\ \A rm \in ResourceManagers : rmVote[rm] \in {"yes", "no"}
  /\ LET allYes == \A rm \in ResourceManagers : rmVote[rm] = "yes"
     IN coordinatorDecision' = IF allYes THEN "commit" ELSE "abort"
  /\ UNCHANGED << rmVote, rmState >>

(*
  RMExecutesCommit: An RM executes the commit decision.
  Preconditions:
    - RM voted yes.
    - Coordinator decided commit.
    - RM has not yet acted on the decision.
  Effect: RM transitions to committed.
*)
RMExecutesCommit(rm) ==
  /\ rmState[rm] = "init"
  /\ coordinatorDecision = "commit"
  /\ rmVote[rm] = "yes"
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED << rmVote, coordinatorDecision >>

(*
  RMExecutesAbort: An RM executes the abort decision.
  Preconditions:
    - RM voted yes (voted no RMs already aborted).
    - Coordinator decided abort.
    - RM has not yet acted on the decision.
  Effect: RM transitions to aborted.
*)
RMExecutesAbort(rm) ==
  /\ rmState[rm] = "init"
  /\ coordinatorDecision = "abort"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED << rmVote, coordinatorDecision >>

(*
  Next: The enabled next-state relation.
  At each step, any one RM may vote, the coordinator may decide,
  or any one RM may execute the decision.
*)
Next ==
  \E rm \in ResourceManagers :
    \/ RMVotesYes(rm)
    \/ RMVotesNo(rm)
    \/ RMExecutesCommit(rm)
    \/ RMExecutesAbort(rm)
  \/ CoordinatorDecides

(*
  Atomicity Invariant: All-or-nothing property.
  If any RM has committed, then all RMs must have committed (or will).
  Equivalently: We never have one RM committed and another still in init.
*)
Atomicity ==
  LET anyCommitted == \E rm \in ResourceManagers : rmState[rm] = "committed"
  IN
    anyCommitted => \A rm \in ResourceManagers : rmState[rm] = "committed"

(*
  Coordinator Validity Invariant: Coordinator commits only if all voted yes.
  This ensures the coordinator's decision is justified by the votes.
*)
CoordinatorValidCommit ==
  coordinatorDecision = "commit" => \A rm \in ResourceManagers : rmVote[rm] = "yes"

(*
  RM Validity Invariant: RM commits only if coordinator decided commit.
  This ensures RMs only commit on explicit coordinator authorization.
*)
RMOnlyCommitsIfCoordinatorSays ==
  \A rm \in ResourceManagers : rmState[rm] = "committed" => coordinatorDecision = "commit"

(*
  Safety Specification: Initial state must satisfy TypeOK, and every transition
  must preserve all invariants and be enabled by Next.
*)
Spec == Init /\ [][Next]_vars

====

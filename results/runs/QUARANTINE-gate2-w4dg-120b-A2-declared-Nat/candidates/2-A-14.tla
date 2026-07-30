---- MODULE ACP_NB ----
EXTENDS Naturals

(* Non-Blocking Atomic Commitment Protocol (ACP-NB) built on top of a   *)
(* simple broadcast variant (ACP-SB).  It adds a reliable broadcast      *)
(* mechanism: a participant that receives a decision forwards it to     *)
(* every other participant before finalizing locally, so a decision     *)
(* can still reach non-crashed participants even if the coordinator     *)
(* dies mid-broadcast.                                                  *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, cphase, coordState, fwd

vars == <<vote, alive, decision, faulty, sentVote, cphase, coordState, fwd>>

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ cphase \in {waiting, doVote}
  /\ coordState \in {idle, requesting, collecting, broadcasting, decided}
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ cphase = waiting
  /\ coordState = idle
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Inherited coordinator actions (same as the simple broadcast protocol).
Request ==
  /\ coordState = idle
  /\ coordState' = requesting
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, cphase, fwd>>

VoteCoordinator ==
  /\ coordState = requesting
  /\ cphase' = doVote
  /\ coordState' = collecting
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, fwd>>

\* A participant may crash silently while collecting votes.
DetectFaultCoordinator ==
  /\ coordState = collecting
  /\ coordState' = decided
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, cphase, fwd>>

MakeDecisionCoordinator ==
  /\ coordState \in {collecting, decided}
  /\ coordState' = broadcasting
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, cphase, fwd>>

BroadcastCoordinator ==
  /\ coordState = broadcasting
  /\ coordState' = decided
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, cphase, fwd>>

DieCoordinator ==
  /\ coordState # idle
  /\ coordState' = idle
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, cphase, fwd>>

\* Participant actions, extending the simple broadcast protocol.
SendVote(p) ==
  /\ alive[p]
  /\ cphase = doVote
  /\ vote[p] = undecided
  /\ sentVote[p] = FALSE
  /\ vote' = [vote EXCEPT ![p] = yes]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, cphase, coordState, fwd>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ cphase = doVote
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, cphase, coordState, fwd>>

\* First pre-decision source: the coordinator's broadcast.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ coordState = decided
  /\ fwd' = [fwd EXCEPT ![p][p] =
                IF \A q \in participants : vote[q] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, cphase, coordState>>

\* Second source: a forward from a different participant.
PreDecideFromFwd(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ \E q \in participants :
       /\ fwd[q][p] # notsent
       /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, cphase, coordState>>

\* Forward the local pre-decision to another participant.
Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, cphase, coordState>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] = fwd[p][p]
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, cphase, coordState, fwd>>

\* Abort only when truly stuck -- nothing alive left to broadcast anything.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordState = decided
  /\ \A q \in participants : fwd[q][p] = notsent
  /\ \A q \in participants : coordState # collecting \/ alive[q]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, cphase, coordState, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, cphase, coordState, fwd>>

Next ==
  \/ Request \/ VoteCoordinator \/ DetectFaultCoordinator
  \/ MakeDecisionCoordinator \/ BroadcastCoordinator \/ DieCoordinator
  \/ \E p \in participants :
       SendVote(p) \/ AbortOnVote(p) \/ PreDecideFromCoord(p)
       \/ PreDecideFromFwd(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)

\* Weak fairness on progress (excluding silent death) is assumed for each     *)
(* participant's progress: sending its vote, pre-deciding from the          *)
(* coordinator, pre-deciding from a forward, forwarding to others, and      *)
(* finalizing a decision.  Coordinator progress (sending a request,        *)
(* collecting votes, broadcasting) is also weakly fair.                     *)
SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : PreDecideFromCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFromFwd(p))
  /\ WF_vars(\E p \in participants : \E q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(Request) /\ WF_vars(VoteCoordinator)
  /\ WF_vars(MakeDecisionCoordinator) /\ WF_vars(BroadcastCoordinator)

\* No two participants ever reach different decisions.
AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)

\* A commit by anyone means everybody voted yes.
AC2 == \A p \in participants :
         decision[p] = commit => \A q \in participants : vote[q] = yes

\* An abort by anyone is justified by a no vote or a fault.
AC3 == \A p \in participants :
         decision[p] = abort =>
           \/ \E q \in participants : vote[q] = no
           \/ \E q \in participants : faulty[q]
           \/ faultyCoord

\* Decisions are permanent once reached.
Irreversible ==
  \A p \in participants :
    (decision[p] = commit \/ decision[p] = abort) ~> decision[p]

TypeInvNB == TypeOK

\* Liveness: the protocol always makes progress toward termination.
AC3Liveness ==
  <>(\A p \in participants : decision[p] # undecided
         \/ \E q \in participants : faulty[q]
         \/ faultyCoord)

\* Liveness: every non-faulty participant eventually reaches a decision.  *)
(* This is the guarantee that the simple broadcast variant lacks, and     *)
(* it comes from the reliable broadcast forwarding.                      *)
AC5 ==
  \A p \in participants : (alive[p] /\ ~faulty[p]) ~> (decision[p] # undecided)

Properties == AC3Liveness /\ AC5

====
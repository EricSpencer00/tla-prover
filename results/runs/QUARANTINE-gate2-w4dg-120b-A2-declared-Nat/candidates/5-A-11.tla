---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB). The coordinator
\* gathers votes, decides, then sends a single decision message to each
\* participant via simple broadcast (sequential, not multicast). Both the
\* coordinator and any participant may crash, and a crash can strand a
\* participant undecided -- this is why the protocol is blocking and does
\* not satisfy the non-blocking termination property AC5 (not modeled here).
\* SAFETY: no two participants ever decide differently (agreement).
\* LIVENESS: every participant or the coordinator eventually fails or decides.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, aliveP, decidedP, faultyP, sentVote,
          sentReq, recv, broadcast, decisionC, aliveC, faultyC

vars == <<vote, aliveP, decidedP, faultyP, sentVote,
          sentReq, recv, broadcast, decisionC, aliveC, faultyC>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ aliveP \in [participants -> BOOLEAN]
  /\ decidedP \in [participants -> {undecided, commit, abort}]
  /\ faultyP \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ sentReq \in [participants -> BOOLEAN]
  /\ recv \in [participants -> {yes, no, waiting}]
  /\ broadcast \in [participants -> {yes, no, notsent}]
  /\ decisionC \in {commit, abort, undecided}
  /\ aliveC \in BOOLEAN
  /\ faultyC \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ aliveP = [p \in participants |-> TRUE]
  /\ decidedP = [p \in participants |-> undecided]
  /\ faultyP = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ sentReq = [p \in participants |-> FALSE]
  /\ recv = [p \in participants |-> waiting]
  /\ broadcast = [p \in participants |-> notsent]
  /\ decisionC = undecided
  /\ aliveC = TRUE
  /\ faultyC = FALSE

\* Coordinator sends a vote request to a participant (only once).
SendRequest(p) ==
  /\ aliveC
  /\ ~sentReq[p]
  /\ sentReq' = [sentReq EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decidedP, faultyP, sentVote,
                recv, broadcast, decisionC, aliveC, faultyC>>

\* Coordinator receives a participant's vote.
RecvVote(p) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ sentReq[p]
  /\ recv[p] = waiting
  /\ sentVote[p]
  /\ recv' = [recv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, aliveP, decidedP, faultyP, sentVote,
                sentReq, broadcast, decisionC, aliveC, faultyC>>

\* Coordinator detects a participant fault and decides abort.
DetectFault(p) ==
  /\ aliveC
  /\ decisionC = undecided
  /\ sentReq[p]
  /\ recv[p] = waiting
  /\ ~aliveP[p]
  /\ decisionC' = abort
  /\ UNCHANGED <<vote, aliveP, decidedP, faultyP, sentVote,
                sentReq, recv, broadcast, aliveC, faultyC>>

MakeDecision ==
  /\ aliveC
  /\ decisionC = undecided
  /\ \A p \in participants : sentReq[p]
  /\ decisionC' = IF \A p \in participants : recv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, aliveP, decidedP, faultyP, sentVote,
                sentReq, recv, broadcast, aliveC, faultyC>>

\* Coordinator broadcasts its decision to a participant (simple broadcast).
SendDecision(p) ==
  /\ aliveC
  /\ decisionC \in {commit, abort}
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = decisionC]
  /\ UNCHANGED <<vote, aliveP, decidedP, faultyP, sentVote,
                sentReq, recv, decisionC, aliveC, faultyC>>

DieCoordinator ==
  /\ aliveC
  /\ aliveC' = FALSE
  /\ faultyC' = TRUE
  /\ UNCHANGED <<vote, aliveP, decidedP, faultyP, sentVote,
                sentReq, recv, broadcast, decisionC, faultyC>>

\* Participant sends its vote to the coordinator.
SendVote(p) ==
  /\ aliveP[p]
  /\ sentReq[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, aliveP, decidedP, faultyP,
                sentReq, recv, broadcast, decisionC, aliveC, faultyC>>

\* A participant may abort unilaterally if its vote is no.
AbortOnVote(p) ==
  /\ aliveP[p]
  /\ decidedP[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decidedP' = [decidedP EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                sentReq, recv, broadcast, decisionC, aliveC, faultyC>>

\* A participant aborts if the coordinator died before requesting its vote.
AbortOnRequestTimeout(p) ==
  /\ aliveP[p]
  /\ decidedP[p] = undecided
  /\ ~sentReq[p]
  /\ ~aliveC
  /\ decidedP' = [decidedP EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                sentReq, recv, broadcast, decisionC, aliveC, faultyC>>

\* A participant adopts the coordinator's broadcasted decision.
DecideOnBroadcast(p) ==
  /\ aliveP[p]
  /\ decidedP[p] = undecided
  /\ broadcast[p] \in {commit, abort}
  /\ decidedP' = [decidedP EXCEPT ![p] = broadcast[p]]
  /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                sentReq, recv, broadcast, decisionC, aliveC, faultyC>>

DieParticipant(p) ==
  /\ aliveP[p]
  /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
  /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decidedP, sentVote,
                sentReq, recv, broadcast, decisionC, aliveC, faultyC>>

CoordinatorProgress == MakeDecision \/ DieCoordinator
ParticipantProgress == \E p \in participants :
  SendVote(p) \/ AbortOnVote(p) \/ AbortOnRequestTimeout(p) \/ DecideOnBroadcast(p)

Next ==
  \/ \E p \in participants :
       SendRequest(p) \/ RecvVote(p) \/ DetectFault(p) \/ SendDecision(p)
       \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnRequestTimeout(p)
       \/ DecideOnBroadcast(p) \/ DieParticipant(p)
  \/ CoordinatorProgress

Spec == Init /\ [][Next]_vars
        /\ WF_vars(CoordinatorProgress)
        /\ WF_vars(ParticipantProgress)

\* No two participants ever decide differently.
Agreement ==
  \A p \in participants, q \in participants :
    (decidedP[p] = commit /\ decidedP[q] = abort) => FALSE

\* A commit requires every participant to have voted yes.
CommitValidity ==
  \A p \in participants : decidedP[p] = commit => \A q \in participants : vote[q] = yes

\* An abort is justified by a no vote, a faulty participant, or a faulty coordinator.
AbortValidity ==
  \A p \in participants : decidedP[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ \E q \in participants : faultyP[q]
    \/ faultyC

\* Once a participant decides, it never changes its mind.
Irrevocability ==
  \A p \in participants :
    /\ (decidedP[p] = commit => decidedP' = [decidedP EXCEPT ![p] = commit])
    /\ (decidedP[p] = abort => decidedP' = [decidedP EXCEPT ![p] = abort])

\* Every participant either decides or fails.
EventualDecision ==
  <>(\E p \in participants : decidedP[p] # undecided \/ faultyP[p] \/ faultyC)

====
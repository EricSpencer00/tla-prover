---- MODULE ACP_SB ----
EXTENDS Naturals

(* Atomic Commitment Protocol with Simple Broadcast (ACP-SB).  This is a   *)
(* time-bounded variant of the classic protocol: it does NOT guarantee   *)
(* termination under coordinator failure, because a crash mid-broadcast  *)
(* leaves some participants undecided.  The spec follows the description  *)
(* literally, including the idiosyncratic failure detection and the      *)
(* weak-fairness assumption on progress actions (excluding death).         *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, aliveP, decisionP, faultyP, sentP,
         sentReq, recv, sentCoord, decisionC, aliveC, faultyC

vars == <<vote, aliveP, decisionP, faultyP, sentP,
          sentReq, recv, sentCoord, decisionC, aliveC, faultyC>>

TypeOK ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ decisionP \in [participants -> {undecided, commit, abort}]
    /\ faultyP \in [participants -> BOOLEAN]
    /\ sentP \in [participants -> BOOLEAN]
    /\ sentReq \in [participants -> BOOLEAN]
    /\ recv \in [participants -> {yes, no, waiting}]
    /\ sentCoord \in [participants -> {commit, abort, notsent}]
    /\ decisionC \in {undecided, commit, abort}
    /\ aliveC \in BOOLEAN
    /\ faultyC \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ decisionP = [p \in participants |-> undecided]
    /\ faultyP = [p \in participants |-> FALSE]
    /\ sentP = [p \in participants |-> FALSE]
    /\ sentReq = [p \in participants |-> FALSE]
    /\ recv = [p \in participants |-> waiting]
    /\ sentCoord = [p \in participants |-> notsent]
    /\ decisionC = undecided
    /\ aliveC = TRUE
    /\ faultyC = FALSE

CoordSendReq(p) ==
    /\ aliveC
    /\ ~sentReq[p]
    /\ sentReq' = [sentReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentP,
                  recv, sentCoord, decisionC, aliveC, faultyC>>

CoordRecvVote(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ sentReq[p]
    /\ recv[p] = waiting
    /\ sentP[p]
    /\ recv' = [recv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentP,
                  sentReq, sentCoord, decisionC, aliveC, faultyC>>

CoordDetectFault(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ sentReq[p]
    /\ recv[p] = waiting
    /\ ~aliveP[p]
    /\ decisionC' = abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentP,
                  sentReq, recv, sentCoord, aliveC, faultyC>>

CoordDecide ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A p \in participants : sentReq[p]
    /\ \A p \in participants : recv[p] # waiting
    /\ decisionC' = IF \A p \in participants : recv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentP,
                  sentReq, recv, sentCoord, aliveC, faultyC>>

CoordSendDecision(p) ==
    /\ aliveC
    /\ decisionC # undecided
    /\ sentCoord[p] = notsent
    /\ sentCoord' = [sentCoord EXCEPT ![p] = decisionC]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentP,
                  sentReq, recv, decisionC, aliveC, faultyC>>

CoordDie ==
    /\ aliveC
    /\ aliveC' = FALSE
    /\ faultyC' = TRUE
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentP,
                  sentReq, recv, sentCoord, decisionC, faultyC>>

PartSendVote(p) ==
    /\ aliveP[p]
    /\ sentReq[p]
    /\ ~sentP[p]
    /\ sentP' = [sentP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP,
                  sentReq, recv, sentCoord, decisionC, aliveC, faultyC>>

PartAbortOnVote(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ sentP[p]
    /\ vote[p] = no
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, sentP,
                  sentReq, recv, sentCoord, decisionC, aliveC, faultyC>>

PartAbortNoReq(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ ~sentReq[p]
    /\ ~aliveC
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, sentP,
                  sentReq, recv, sentCoord, decisionC, aliveC, faultyC>>

PartDecide(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ sentCoord[p] # notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = sentCoord[p]]
    /\ UNCHANGED <<vote, aliveP, faultyP, sentP,
                  sentReq, recv, sentCoord, decisionC, aliveC, faultyC>>

PartDie(p) ==
    /\ aliveP[p]
    /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
    /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decisionP, sentP,
                  sentReq, recv, sentCoord, decisionC, aliveC, faultyC>>

Next ==
    \/ \E p \in participants : CoordSendReq(p)
    \/ \E p \in participants : CoordRecvVote(p)
    \/ \E p \in participants : CoordDetectFault(p)
    \/ CoordDecide
    \/ \E p \in participants : CoordSendDecision(p)
    \/ CoordDie
    \/ \E p \in participants : PartSendVote(p)
    \/ \E p \in participants : PartAbortOnVote(p)
    \/ \E p \in participants : PartAbortNoReq(p)
    \/ \E p \in participants : PartDecide(p)
    \/ \E p \in participants : PartDie(p)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A p \in participants :
        /\ WF_vars(PartSendVote(p))
        /\ WF_vars(PartAbortOnVote(p))
        /\ WF_vars(PartDecide(p))
    /\ WF_vars(CoordDecide)

(* Safety: no two participants ever decide differently.                 *)
NoTwoDecideDifferently ==
    \A p, q \in participants :
        (decisionP[p] = commit /\ decisionP[q] = abort) => p = q

(* Safety: a commit can only be reached if every participant voted yes. *)
CommitOnlyOnUnanimousYes ==
    \A p \in participants : decisionP[p] = commit => \A q \in participants : vote[q] = yes

(* Safety: an abort is always justified by a no vote or a crash.         *)
AbortOnlyOnNoOrCrash ==
    \A p \in participants : decisionP[p] = abort =>
        \/ \E q \in participants : vote[q] = no
        \/ \E q \in participants : faultyP[q]
        \/ faultyC

(* Safety: a participant decides at most once.                           *)
DecideAtMostOnce ==
    \A p \in participants : (decisionP[p] = commit) ~> (decisionP[p] = commit)
                          /\ (decisionP[p] = abort) ~> (decisionP[p] = abort)

(* Liveness: every participant eventually decides, or a crash happens.   *)
DecideOrCrash ==
    <>(\A p \in participants : decisionP[p] # undecided \/ faultyP[p] \/ faultyC)
====
---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME participants # {}
ASSUME yes # no
ASSUME commit # abort

VARIABLES vote, aliveP, decisionP, faultyP, sentVote
VARIABLES sentReq, recv, broadcasted, decisionC, aliveC, faultyC

vars == <<vote, aliveP, decisionP, faultyP, sentVote,
          sentReq, recv, broadcasted, decisionC, aliveC, faultyC>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ decisionP \in [participants -> {undecided, commit, abort}]
    /\ faultyP \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ sentReq \in [participants -> BOOLEAN]
    /\ recv \in [participants -> {yes, no, waiting}]
    /\ broadcasted \in [participants -> {commit, abort, notsent}]
    /\ decisionC \in {undecided, commit, abort}
    /\ aliveC \in BOOLEAN
    /\ faultyC \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ decisionP = [p \in participants |-> undecided]
    /\ faultyP = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ sentReq = [p \in participants |-> FALSE]
    /\ recv = [p \in participants |-> waiting]
    /\ broadcasted = [p \in participants |-> notsent]
    /\ decisionC = undecided
    /\ aliveC = TRUE
    /\ faultyC = FALSE

SendReq(p) ==
    /\ aliveC
    /\ ~sentReq[p]
    /\ sentReq' = [sentReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                  recv, broadcasted, decisionC, aliveC, faultyC>>

ReceiveVote(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A q \in participants: sentReq[q]
    /\ recv[p] = waiting
    /\ sentVote[p]
    /\ recv' = [recv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                  sentReq, broadcasted, decisionC, aliveC, faultyC>>

DetectFault(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A q \in participants: sentReq[q]
    /\ recv[p] = waiting
    /\ ~aliveP[p]
    /\ decisionC' = abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                  sentReq, recv, broadcasted, aliveC, faultyC>>

MakeDecision ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A p \in participants: recv[p] # waiting
    /\ decisionC' = (IF \A p \in participants: recv[p] = yes THEN commit ELSE abort)
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                  sentReq, recv, broadcasted, aliveC, faultyC>>

Broadcast(p) ==
    /\ aliveC
    /\ decisionC # undecided
    /\ broadcasted[p] = notsent
    /\ broadcasted' = [broadcasted EXCEPT ![p] = decisionC]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                  sentReq, recv, decisionC, aliveC, faultyC>>

DieCoordinator ==
    /\ aliveC
    /\ aliveC' = FALSE
    /\ faultyC' = TRUE
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                  sentReq, recv, broadcasted, decisionC, aliveC, faultyC>>

SendVote(p) ==
    /\ aliveP[p]
    /\ sentReq[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP,
                  sentReq, recv, broadcasted, decisionC, aliveC, faultyC>>

AbortOnVote(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                  sentReq, recv, broadcasted, decisionC, aliveC, faultyC>>

AbortOnTimeout(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ ~sentReq[p]
    /\ ~aliveC
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                  sentReq, recv, broadcasted, decisionC, aliveC, faultyC>>

Decide(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ broadcasted[p] # notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = broadcasted[p]]
    /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                  sentReq, recv, broadcasted, decisionC, aliveC, faultyC>>

DieParticipant(p) ==
    /\ aliveP[p]
    /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
    /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decisionP, sentVote,
                  sentReq, recv, broadcasted, decisionC, aliveC, faultyC>>

Next ==
    \/ \E p \in participants: SendReq(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ Broadcast(p)
    \/ \E p \in participants: SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ Decide(p) \/ DieParticipant(p)
    \/ MakeDecision
    \/ DieCoordinator

Spec == Init /\ [][Next]_vars
     /\ WF_vars(\E p \in participants: SendReq(p))
     /\ WF_vars(\E p \in participants: SendVote(p))
     /\ WF_vars(\E p \in participants: Decide(p))

Agreement ==
    \A p1, p2 \in participants:
        (decisionP[p1] = commit /\ decisionP[p2] = abort) => FALSE

CommitValid ==
    \A p \in participants:
        decisionP[p] = commit => (\A q \in participants: vote[q] = yes)

AbortValid ==
    \A p \in participants:
        decisionP[p] = abort =>
            \/ \E q \in participants: vote[q] = no
            \/ \E q \in participants: faultyP[q]
            \/ faultyC

Irreversible ==
    \A p \in participants:
        /\ (decisionP[p] = commit ~> decisionP[p] = commit)
        /\ (decisionP[p] = abort ~> decisionP[p] = abort)

EventualDecision ==
    <>(\A p \in participants: decisionP[p] # undecided \/ faultyP[p] \/ faultyC)

====
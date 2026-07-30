---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, aliveP, decisionP, faultyP, voteSent, requestSent, recvVote, sentDecision, decisionC, aliveC, faultyC

vars == <<vote, aliveP, decisionP, faultyP, voteSent, requestSent, recvVote, sentDecision, decisionC, aliveC, faultyC>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ decisionP \in [participants -> {undecided, commit, abort}]
    /\ faultyP \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ requestSent \in [participants -> BOOLEAN]
    /\ recvVote \in [participants -> {yes, no, waiting}]
    /\ sentDecision \in [participants -> {commit, abort, notsent}]
    /\ decisionC \in {undecided, commit, abort}
    /\ aliveC \in BOOLEAN
    /\ faultyC \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ decisionP = [p \in participants |-> undecided]
    /\ faultyP = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ requestSent = [p \in participants |-> FALSE]
    /\ recvVote = [p \in participants |-> waiting]
    /\ sentDecision = [p \in participants |-> notsent]
    /\ decisionC = undecided
    /\ aliveC = TRUE
    /\ faultyC = FALSE

SendRequest(p) ==
    /\ aliveC
    /\ ~requestSent[p]
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voteSent, recvVote, sentDecision, decisionC, aliveC, faultyC>>

ReceiveVote(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A q \in participants : requestSent[q]
    /\ recvVote[p] = waiting
    /\ voteSent[p]
    /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voteSent, requestSent, sentDecision, decisionC, aliveC, faultyC>>

DetectFault(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A q \in participants : requestSent[q]
    /\ recvVote[p] = waiting
    /\ ~aliveP[p]
    /\ decisionC' = abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voteSent, requestSent, recvVote, sentDecision, aliveC, faultyC>>

MakeDecision ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A p \in participants : recvVote[p] # waiting
    /\ decisionC' = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voteSent, requestSent, recvVote, sentDecision, aliveC, faultyC>>

Broadcast(p) ==
    /\ aliveC
    /\ decisionC # undecided
    /\ sentDecision[p] = notsent
    /\ sentDecision' = [sentDecision EXCEPT ![p] = decisionC]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voteSent, requestSent, recvVote, decisionC, aliveC, faultyC>>

DieCoordinator ==
    /\ aliveC
    /\ aliveC' = FALSE
    /\ faultyC' = TRUE
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voteSent, requestSent, recvVote, sentDecision, decisionC, aliveC, faultyC>>

SendVote(p) ==
    /\ aliveP[p]
    /\ requestSent[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, requestSent, recvVote, sentDecision, decisionC, aliveC, faultyC>>

DecideUnilaterallyAbort(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ voteSent[p]
    /\ vote[p] = no
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, voteSent, requestSent, recvVote, sentDecision, decisionC, aliveC, faultyC>>

DecideOnBroadcast(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ sentDecision[p] # notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = sentDecision[p]]
    /\ UNCHANGED <<vote, aliveP, faultyP, voteSent, requestSent, recvVote, sentDecision, decisionC, aliveC, faultyC>>

TimeoutAbort(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ ~aliveC
    /\ ~requestSent[p]
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, voteSent, requestSent, recvVote, sentDecision, decisionC, aliveC, faultyC>>

DieParticipant(p) ==
    /\ aliveP[p]
    /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
    /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decisionP, voteSent, requestSent, recvVote, sentDecision, decisionC, aliveC, faultyC>>

Decide ==
    \/ \E p \in participants : DecideUnilaterallyAbort(p) \/ DecideOnBroadcast(p) \/ TimeoutAbort(p)

Next ==
    \/ \E p \in participants : SendRequest(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ Broadcast(p) \/ DieParticipant(p)
    \/ MakeDecision
    \/ DieCoordinator
    \/ \E p \in participants : SendVote(p) \/ Decide(p)

FairParticipantProgress ==
    /\ \A p \in participants : WF_vars(SendVote(p) \/ Decide(p))
    /\ \A p \in participants : WF_vars(DecideOnBroadcast(p))
    /\ \A p \in participants : WF_vars(TimeoutAbort(p))

FairCoordinatorProgress ==
    /\ WF_vars(SendRequest("dummy") \/ MakeDecision) \/ WF_vars(Broadcast("dummy"))

Spec == Init /\ [][Next]_vars /\ FairCoordinatorProgress /\ FairParticipantProgress

Agreement ==
    \A p, q \in participants : (decisionP[p] = commit /\ decisionP[q] = abort) => FALSE

CommitValidity ==
    \A p \in participants : decisionP[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValidity ==
    \A p \in participants : decisionP[p] = abort =>
        \/ \E q \in participants : vote[q] = no
        \/ \E q \in participants : faultyP[q]
        \/ faultyC

Irreversibility ==
    \A p \in participants : decisionP[p] = commit => (decisionP[p] = commit) /\ (decisionP[p] = abort => (decisionP[p] = abort))

EventuallyDecideOrSomeFault ==
    <>(\A p \in participants : decisionP[p] # undecided \/ faultyP[p]) \/ faultyC

====
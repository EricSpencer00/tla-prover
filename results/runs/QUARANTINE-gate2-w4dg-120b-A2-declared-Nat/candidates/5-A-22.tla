---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, aliveP, decisionP, faultyP, voted, reqsent, recvvote, sentdecide, coorddec, aliveC, faultyC

vars == <<vote, aliveP, decisionP, faultyP, voted, reqsent, recvvote, sentdecide, coorddec, aliveC, faultyC>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ decisionP \in [participants -> {undecided, commit, abort}]
    /\ faultyP \in [participants -> BOOLEAN]
    /\ voted \in [participants -> BOOLEAN]
    /\ reqsent \in [participants -> BOOLEAN]
    /\ recvvote \in [participants -> {yes, no, waiting}]
    /\ sentdecide \in [participants -> {commit, abort, notsent}]
    /\ coorddec \in {undecided, commit, abort}
    /\ aliveC \in BOOLEAN
    /\ faultyC \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ decisionP = [p \in participants |-> undecided]
    /\ faultyP = [p \in participants |-> FALSE]
    /\ voted = [p \in participants |-> FALSE]
    /\ reqsent = [p \in participants |-> FALSE]
    /\ recvvote = [p \in participants |-> waiting]
    /\ sentdecide = [p \in participants |-> notsent]
    /\ coorddec = undecided
    /\ aliveC = TRUE
    /\ faultyC = FALSE

\* Coordinator actions
SendReq(p) ==
    /\ aliveC
    /\ ~reqsent[p]
    /\ reqsent' = [reqsent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voted, recvvote, sentdecide, coorddec, aliveC, faultyC>>

RecvVote(p) ==
    /\ aliveC
    /\ coorddec = undecided
    /\ reqsent[p]
    /\ recvvote[p] = waiting
    /\ voted[p]
    /\ recvvote' = [recvvote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voted, reqsent, sentdecide, coorddec, aliveC, faultyC>>

DetectFault(p) ==
    /\ aliveC
    /\ coorddec = undecided
    /\ reqsent[p]
    /\ recvvote[p] = waiting
    /\ ~aliveP[p]
    /\ coorddec' = abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voted, reqsent, recvvote, sentdecide, aliveC, faultyC>>

MakeDecision ==
    /\ aliveC
    /\ coorddec = undecided
    /\ \A p \in participants : recvvote[p] # waiting
    /\ coorddec' = IF \A p \in participants : recvvote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voted, reqsent, recvvote, sentdecide, aliveC, faultyC>>

Broadcast(p) ==
    /\ aliveC
    /\ coorddec # undecided
    /\ sentdecide[p] = notsent
    /\ sentdecide' = [sentdecide EXCEPT ![p] = coorddec]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voted, reqsent, recvvote, coorddec, aliveC, faultyC>>

DieCoordinator ==
    /\ aliveC
    /\ aliveC' = FALSE
    /\ faultyC' = TRUE
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, voted, reqsent, recvvote, sentdecide, coorddec>>

\* Participant actions
SendVote(p) ==
    /\ aliveP[p]
    /\ reqsent[p]
    /\ ~voted[p]
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, reqsent, recvvote, sentdecide, coorddec, aliveC, faultyC>>

AbortOnVote(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ voted[p]
    /\ vote[p] = no
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, voted, reqsent, recvvote, sentdecide, coorddec, aliveC, faultyC>>

AbortOnTimeout(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ ~reqsent[p]
    /\ ~aliveC
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, voted, reqsent, recvvote, sentdecide, coorddec, aliveC, faultyC>>

DecideFromBroadcast(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ sentdecide[p] # notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = sentdecide[p]]
    /\ UNCHANGED <<vote, aliveP, faultyP, voted, reqsent, recvvote, sentdecide, coorddec, aliveC, faultyC>>

DieParticipant(p) ==
    /\ aliveP[p]
    /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
    /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decisionP, voted, reqsent, recvvote, sentdecide, coorddec, aliveC, faultyC>>

CoordNext ==
    \/ \E p \in participants : SendReq(p)
    \/ \E p \in participants : RecvVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ DieCoordinator

PartNext ==
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideFromBroadcast(p)
    \/ \E p \in participants : DieParticipant(p)

Next == CoordNext \/ PartNext

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in participants : SendReq(p))
        /\ WF_vars(\E p \in participants : SendVote(p))
        /\ WF_vars(\E p \in participants : DecideFromBroadcast(p))

\* No two participants decide differently.
Aggreement ==
    \A p, q \in participants :
        (decisionP[p] = commit /\ decisionP[q] = abort) => FALSE

\* Commit is only possible if everyone voted yes.
CommitValidity ==
    \A p \in participants : decisionP[p] = commit => (\A q \in participants : vote[q] = yes)

\* Abort is only possible if there is a no vote or a crash.
AbortValidity ==
    \A p \in participants :
        decisionP[p] = abort =>
            \/ \E q \in participants : vote[q] = no
            \/ \E q \in participants : faultyP[q]
            \/ faultyC

\* Decisions are final and one-way.
Irreversible ==
    \A p \in participants :
        /\ decisionP[p] = commit => \A m \in participants : decisionP[m] = commit \/ decisionP[m] = undo
        /\ decisionP[p] = abort => \A m \in participants : decisionP[m] = abort \/ decisionP[m] = undo

\* Blocking termination: everyone decides, or there is a crash.
EventualDecisionOrCrash ==
    <>(\A p \in participants : decisionP[p] # undecided \/ faultyP[p]) \/ faultyC

====
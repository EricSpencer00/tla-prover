---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, aliveP, decisionP, pFaulty, sentVote, voteReqSent,
          recvVote, sentDecision, decision, aliveC, cFaulty

vars == <<vote, aliveP, decisionP, pFaulty, sentVote, voteReqSent,
           recvVote, sentDecision, decision, aliveC, cFaulty>>

TypeOK ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ decisionP \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ voteReqSent \in [participants -> BOOLEAN]
    /\ recvVote \in [participants -> {yes, no, waiting}]
    /\ sentDecision \in [participants -> {commit, abort, notsent}]
    /\ decision \in {undecided, commit, abort}
    /\ aliveC \in BOOLEAN
    /\ cFaulty \in BOOLEAN

Init ==
    /\ \E v \in {yes, no} : vote = [p \in participants |-> v]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ decisionP = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ voteReqSent = [p \in participants |-> FALSE]
    /\ recvVote = [p \in participants |-> waiting]
    /\ sentDecision = [p \in participants |-> notsent]
    /\ decision = undecided
    /\ aliveC = TRUE
    /\ cFaulty = FALSE

SendVoteRequest(p) ==
    /\ aliveC
    /\ ~voteReqSent[p]
    /\ voteReqSent' = [voteReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, pFaulty, sentVote,
                   recvVote, sentDecision, decision, aliveC, cFaulty>>

ReceiveVote(p) ==
    /\ aliveC
    /\ decision = undecided
    /\ \A q \in participants : voteReqSent[q]
    /\ recvVote[p] = waiting
    /\ sentVote[p]
    /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, aliveP, decisionP, pFaulty, sentVote,
                   voteReqSent, sentDecision, decision, aliveC, cFaulty>>

DetectParticipantFault(p) ==
    /\ aliveC
    /\ decision = undecided
    /\ \A q \in participants : voteReqSent[q]
    /\ recvVote[p] = waiting
    /\ ~aliveP[p]
    /\ decision' = abort
    /\ UNCHANGED <<vote, aliveP, decisionP, pFaulty, sentVote,
                   voteReqSent, recvVote, sentDecision, aliveC, cFaulty>>

MakeDecision ==
    /\ aliveC
    /\ decision = undecided
    /\ \A p \in participants : recvVote[p] # waiting
    /\ decision' = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, aliveP, decisionP, pFaulty, sentVote,
                   voteReqSent, recvVote, sentDecision, aliveC, cFaulty>>

BroadcastDecision(p) ==
    /\ aliveC
    /\ decision # undecided
    /\ sentDecision[p] = notsent
    /\ sentDecision' = [sentDecision EXCEPT ![p] = decision]
    /\ UNCHANGED <<vote, aliveP, decisionP, pFaulty, sentVote,
                   voteReqSent, recvVote, decision, aliveC, cFaulty>>

DieC ==
    /\ aliveC
    /\ aliveC' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<vote, aliveP, decisionP, pFaulty, sentVote,
                   voteReqSent, recvVote, sentDecision, decision>>

SendVote(p) ==
    /\ aliveP[p]
    /\ ~sentVote[p]
    /\ voteReqSent[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, pFaulty, voteReqSent,
                   recvVote, sentDecision, decision, aliveC, cFaulty>>

AbortOnVote(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, pFaulty, sentVote,
                   voteReqSent, recvVote, sentDecision, decision, aliveC, cFaulty>>

AbortOnTimeout(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ ~aliveC
    /\ ~voteReqSent[p]
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, pFaulty, sentVote,
                   voteReqSent, recvVote, sentDecision, decision, aliveC, cFaulty>>

DecideFromCoordinator(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ sentDecision[p] # notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = sentDecision[p]]
    /\ UNCHANGED <<vote, aliveP, pFaulty, sentVote,
                   voteReqSent, recvVote, sentDecision, decision, aliveC, cFaulty>>

DieP(p) ==
    /\ aliveP[p]
    /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decisionP, sentVote, voteReqSent,
                   recvVote, sentDecision, decision, aliveC, cFaulty>>

Next ==
    \/ \E p \in participants : SendVoteRequest(p) \/ ReceiveVote(p)
                                \/ DetectParticipantFault(p) \/ BroadcastDecision(p)
                                \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p)
                                \/ DecideFromCoordinator(p) \/ DieP(p)
    \/ MakeDecision
    \/ DieC

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : AbortOnVote(p))
    /\ WF_vars(\E p \in participants : Deciding(p))

Deciding(p) == SendVote(p) \/ AbortOnVote(p)

AC1 == \A p1, p2 \in participants : ~(decisionP[p1] = commit /\ decisionP[p2] = abort)
AC2 == (\E p \in participants : decisionP[p] = commit) => (\A p \in participants : vote[p] = yes)
AC3 == (\E p \in participants : decisionP[p] = abort)
          => (\E p \in participants : vote[p] = no) \/ (\E p \in participants : pFaulty[p]) \/ cFaulty
AC4 == \A p \in participants : (decisionP[p] = commit) ~> (decisionP[p] = commit)

TypeInv == TypeOK
Liveness == AC3

====
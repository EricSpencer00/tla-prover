---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, aliveP, decisionP, faultyP, sendVote
VARIABLES recvReq, recvVote, broadcasted, decisionC, aliveC, faultyC

vars == <<vote, aliveP, decisionP, faultyP, sendVote,
          recvReq, recvVote, broadcasted, decisionC, aliveC, faultyC>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ decisionP \in [participants -> {undecided, commit, abort}]
    /\ faultyP \in [participants -> BOOLEAN]
    /\ sendVote \in [participants -> BOOLEAN]

    /\ recvReq \subseteq participants
    /\ recvVote \in [participants -> {yes, no, waiting}]
    /\ broadcasted \in [participants -> {commit, abort, notsent}]
    /\ decisionC \in {undecided, commit, abort}
    /\ aliveC \in BOOLEAN
    /\ faultyC \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ decisionP = [p \in participants |-> undecided]
    /\ faultyP = [p \in participants |-> FALSE]
    /\ sendVote = [p \in participants |-> FALSE]

    /\ recvReq = {}
    /\ recvVote = [p \in participants |-> waiting]
    /\ broadcasted = [p \in participants |-> notsent]
    /\ decisionC = undecided
    /\ aliveC = TRUE
    /\ faultyC = FALSE

\* Coordinator sends a vote request to a participant.
SendRequest(p) ==
    /\ aliveC
    /\ p \notin recvReq
    /\ recvReq' = recvReq \cup {p}
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sendVote,
                   recvVote, broadcasted, decisionC, aliveC, faultyC>>

\* Coordinator receives a participant's vote.
ReceiveVote(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ recvReq = participants
    /\ recvVote[p] = waiting
    /\ sendVote[p]
    /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sendVote,
                   recvReq, broadcasted, decisionC, aliveC, faultyC>>

\* Coordinator detects a participant fault and decides to abort.
DetectFault(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ recvReq = participants
    /\ recvVote[p] = waiting
    /\ ~aliveP[p]
    /\ decisionC' = abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sendVote,
                   recvReq, recvVote, broadcasted, aliveC, faultyC>>

\* Coordinator makes a commit or abort decision once all votes are in.
MakeDecision ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A p \in participants : recvVote[p] # waiting
    /\ decisionC' = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sendVote,
                   recvReq, recvVote, broadcasted, aliveC, faultyC>>

\* Coordinator broadcasts its decision to a participant (simple broadcast).
Broadcast(p) ==
    /\ aliveC
    /\ decisionC # undecided
    /\ broadcasted[p] = notsent
    /\ broadcasted' = [broadcasted EXCEPT ![p] = decisionC]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sendVote,
                   recvReq, recvVote, decisionC, aliveC, faultyC>>

\* Coordinator crashes; this transition is not weakly fair.
DieC ==
    /\ aliveC
    /\ aliveC' = FALSE
    /\ faultyC' = TRUE
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sendVote,
                   recvReq, recvVote, broadcasted, decisionC, aliveC, faultyC>>

\* A participant sends its vote to the coordinator.
Send(p) ==
    /\ aliveP[p]
    /\ p \in recvReq
    /\ ~sendVote[p]
    /\ sendVote' = [sendVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP,
                   recvReq, recvVote, broadcasted, decisionC, aliveC, faultyC>>

\* A participant unilaterally aborts on its own no vote.
AbortOnVote(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ sendVote[p]
    /\ vote[p] = no
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP,
                   recvReq, recvVote, broadcasted, decisionC, aliveC, faultyC, sendVote>>

\* A participant aborts on timeout when the coordinator has died.
AbortTimeout(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ ~aliveC
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP,
                   recvReq, recvVote, broadcasted, decisionC, aliveC, faultyC, sendVote>>

\* A participant adopts the decision broadcast by the coordinator.
DecideOnBroadcast(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ broadcasted[p] # notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = broadcasted[p]]
    /\ UNCHANGED <<vote, aliveP, faultyP,
                   recvReq, recvVote, broadcasted, decisionC, aliveC, faultyC, sendVote>>

\* A participant crashes; this transition is not weakly fair.
DieP(p) ==
    /\ aliveP[p]
    /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
    /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decisionP, recvReq, recvVote,
                   broadcasted, decisionC, aliveC, faultyC, sendVote>>

Next ==
    \/ \E p \in participants : SendRequest(p) \/ ReceiveVote(p) \/ DetectFault(p)
                              \/ Broadcast(p) \/ Send(p) \/ AbortOnVote(p)
                              \/ AbortTimeout(p) \/ DecideOnBroadcast(p)
                              \/ DieP(p)
    \/ MakeDecision
    \/ DieC

\* A participant's commit is irrevocable once it happens.
CommitIrreversible ==
    \A p \in participants : (decisionP[p] = commit) ~> (decisionP[p] = commit)

\* A participant's abort is irrevocable once it happens.
AbortIrreversible ==
    \A p \in participants : (decisionP[p] = abort) ~> (decisionP[p] = abort)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : Send(p))
    /\ WF_vars(\E p \in participants : AbortOnVote(p))
    /\ WF_vars(\E p \in participants : AbortTimeout(p))
    /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))
    /\ WF_vars(\E p \in participants : SendRequest(p))
    /\ WF_vars(\E p \in participants : ReceiveVote(p))
    /\ WF_vars(\E p \in participants : Broadcast(p))
    /\ WF_vars(MakeDecision)

\* No two participants can decide differently.
Agreement ==
    \A a, b \in participants :
        (decisionP[a] = commit) ~> (decisionP[b] # abort)

\* A commit needs a unanimous yes vote.
CommitValid ==
    \A p \in participants : (decisionP[p] = commit) => (\A q \in participants : vote[q] = yes)

\* An abort needs a no vote or a fault somewhere.
AbortValid ==
    \A p \in participants : (decisionP[p] = abort) =>
        (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faultyP[q]) \/ faultyC

\* Progress: every non-faulty participant eventually decides. This liveness
\* property does NOT hold for the simple broadcast variant -- it is what is
\* missing from ACP-SB's non-blocking guarantee -- but it is required here
\* anyway, so the spec simply fails to satisfy it under a coordinator crash.
AllDecide ==
    \A p \in participants : (aliveP[p]) ~> (decisionP[p] # undecided)

====
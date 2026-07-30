---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
    participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
    voteP, aliveP, decisionP, faultyP, sentVote,
    requested, voteC, broadcasted, decisionC, aliveC, faultyC

vars == <<
    voteP, aliveP, decisionP, faultyP, sentVote,
    requested, voteC, broadcasted, decisionC, aliveC, faultyC
>>

TypeInv ==
    /\ voteP \in [participants -> {yes, no}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ decisionP \in [participants -> {undecided, commit, abort}]
    /\ faultyP \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ requested \in [participants -> BOOLEAN]
    /\ voteC \in [participants -> {yes, no, waiting}]
    /\ broadcasted \in [participants -> {commit, abort, notsent}]
    /\ decisionC \in {undecided, commit, abort}
    /\ aliveC \in BOOLEAN
    /\ faultyC \in BOOLEAN

Init ==
    /\ voteP \in [participants -> {yes, no}]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ decisionP = [p \in participants |-> undecided]
    /\ faultyP = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ requested = [p \in participants |-> FALSE]
    /\ voteC = [p \in participants |-> waiting]
    /\ broadcasted = [p \in participants |-> notsent]
    /\ decisionC = undecided
    /\ aliveC = TRUE
    /\ faultyC = FALSE

CoordSendRequest(p) ==
    /\ aliveC
    /\ ~requested[p]
    /\ requested' = [requested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<voteP, aliveP, decisionP, faultyP, sentVote,
                  voteC, broadcasted, decisionC, aliveC, faultyC>>

CoordReceiveVote(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A q \in participants : requested[q]
    /\ voteC[p] = waiting
    /\ sentVote[p]
    /\ voteC' = [voteC EXCEPT ![p] = voteP[p]]
    /\ UNCHANGED <<voteP, aliveP, decisionP, faultyP, sentVote,
                  requested, broadcasted, decisionC, aliveC, faultyC>>

CoordDetectFault(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A q \in participants : requested[q]
    /\ voteC[p] = waiting
    /\ ~aliveP[p]
    /\ decisionC' = abort
    /\ UNCHANGED <<voteP, aliveP, decisionP, faultyP, sentVote,
                  requested, voteC, broadcasted, aliveC, faultyC>>

CoordMakeDecision ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A p \in participants : voteC[p] # waiting
    /\ decisionC' = IF \A p \in participants : voteC[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<voteP, aliveP, decisionP, faultyP, sentVote,
                  requested, voteC, broadcasted, aliveC, faultyC>>

CoordBroadcast(p) ==
    /\ aliveC
    /\ decisionC # undecided
    /\ broadcasted[p] = notsent
    /\ broadcasted' = [broadcasted EXCEPT ![p] = decisionC]
    /\ UNCHANGED <<voteP, aliveP, decisionP, faultyP, sentVote,
                  requested, voteC, decisionC, aliveC, faultyC>>

CoordDie ==
    /\ aliveC
    /\ aliveC' = FALSE
    /\ faultyC' = TRUE
    /\ UNCHANGED <<voteP, aliveP, decisionP, faultyP, sentVote,
                  requested, voteC, broadcasted, decisionC, aliveC>>

CoordStep ==
    \/ \E p \in participants : CoordSendRequest(p)
    \/ \E p \in participants : CoordReceiveVote(p)
    \/ \E p \in participants : CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants : CoordBroadcast(p)
    \/ CoordDie

PartSendVote(p) ==
    /\ aliveP[p]
    /\ requested[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<voteP, aliveP, decisionP, faultyP,
                  requested, voteC, broadcasted, decisionC, aliveC, faultyC>>

PartAbortOnVote(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ sentVote[p]
    /\ voteP[p] = no
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<voteP, aliveP, faultyP, sentVote,
                  requested, voteC, broadcasted, decisionC, aliveC, faultyC>>

PartAbortOnMissingRequest(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ ~requested[p]
    /\ ~aliveC
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<voteP, aliveP, faultyP, sentVote,
                  requested, voteC, broadcasted, decisionC, aliveC, faultyC>>

PartDecideOnBroadcast(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ broadcasted[p] # notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = broadcasted[p]]
    /\ UNCHANGED <<voteP, aliveP, faultyP, sentVote,
                  requested, voteC, broadcasted, decisionC, aliveC, faultyC>>

PartDie(p) ==
    /\ aliveP[p]
    /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
    /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<voteP, decisionP, sentVote,
                  requested, voteC, broadcasted, decisionC, aliveC, faultyC>>

PartStep ==
    \/ \E p \in participants : PartSendVote(p)
    \/ \E p \in participants : PartAbortOnVote(p)
    \/ \E p \in participants : PartAbortOnMissingRequest(p)
    \/ \E p \in participants : PartDecideOnBroadcast(p)
    \/ \E p \in participants : PartDie(p)

Next ==
    \/ CoordStep
    \/ PartStep

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CoordMakeDecision)
    /\ WF_vars(CoordBroadcast(\E p \in participants : p))
    /\ \A p \in participants : WF_vars(PartSendVote(p))
    /\ \A p \in participants : WF_vars(PartDecideOnBroadcast(p))

AC1 ==
    /\ \A p \in participants : decisionP[p] = commit => (\A q \in participants : decisionP[q] = commit)
    /\ \A p \in participants : decisionP[p] = abort => (\A q \in participants : decisionP[q] = abort)

AC2 ==
    \E p \in participants : decisionP[p] = commit => (\A q \in participants : voteP[q] = yes)

AC3 ==
    \E p \in participants : decisionP[p] = abort => (\E q \in participants : voteP[q] = no \/ faultyP[q] \/ faultyC)

AC4 ==
    /\ \A p \in participants : (decisionP[p] = commit) ~> (decisionP[p] = commit)
    /\ \A p \in participants : (decisionP[p] = abort) ~> (decisionP[p] = abort)

AC3Liveness ==
    <>(\A p \in participants : decisionP[p] # undecided \/ faultyP[p] \/ faultyC)

====
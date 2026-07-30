---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, aliveP, decisionP, faultyP, sentVote,
         w4vote, w4coord, decisionC, aliveC, faultyC

vars == <<vote, aliveP, decisionP, faultyP, sentVote,
          w4vote, w4coord, decisionC, aliveC, faultyC>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ decisionP \in [participants -> {undecided, commit, abort}]
    /\ faultyP \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ w4vote \in [participants -> {yes, no, waiting}]
    /\ w4coord \in [participants -> {yes, no, waiting}]
    /\ decisionC \in {undecided, commit, abort}
    /\ aliveC \in BOOLEAN
    /\ faultyC \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ decisionP = [p \in participants |-> undecided]
    /\ faultyP = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ w4vote = [p \in participants |-> waiting]
    /\ w4coord = [p \in participants |-> notsent]
    /\ decisionC = undecided
    /\ aliveC = TRUE
    /\ faultyC = FALSE

\* The coordinator sends the vote request to a participant.
RequestVote(p) ==
    /\ aliveC
    /\ w4coord[p] = notsent
    /\ w4coord' = [w4coord EXCEPT ![p] = notsent]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                   w4vote, decisionC, aliveC, faultyC>>

\* The coordinator receives a vote from a participant.
RecvVote(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A q \in participants : w4coord[q] # notsent
    /\ w4vote[p] = waiting
    /\ sentVote[p]
    /\ w4vote' = [w4vote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                   w4coord, decisionC, aliveC, faultyC>>

\* The coordinator detects that a participant has died without voting and aborts.
DetectFault(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A q \in participants : w4coord[q] # notsent
    /\ w4vote[p] = waiting
    /\ ~aliveP[p]
    /\ decisionC' = abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                   w4vote, w4coord, aliveC, faultyC>>

\* The coordinator makes a commit/abort decision once all votes are in.
MakeDecision ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A p \in participants : w4vote[p] # waiting
    /\ decisionC' = IF \A p \in participants : w4vote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                   w4vote, w4coord, aliveC, faultyC>>

\* Simple broadcast: the coordinator sends its decision to one participant.
BroadcastDecision(p) ==
    /\ aliveC
    /\ decisionC # undecided
    /\ w4coord[p] = notsent
    /\ w4coord' = [w4coord EXCEPT ![p] = decisionC]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                   w4vote, decisionC, aliveC, faultyC>>

\* The coordinator crashes.
DieCoordinator ==
    /\ aliveC
    /\ aliveC' = FALSE
    /\ faultyC' = TRUE
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, sentVote,
                   w4vote, w4coord, decisionC, aliveC, faultyC>>

\* A participant sends its vote to the coordinator.
SendVote(p) ==
    /\ aliveP[p]
    /\ w4coord[p] # notsent
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP,
                   w4vote, w4coord, decisionC, aliveC, faultyC>>

\* A participant votes no and aborts unilaterally.
AbortOnVote(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                   w4vote, w4coord, decisionC, aliveC, faultyC>>

\* A participant aborts because the coordinator died before requesting.
AbortReqTimeout(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ ~aliveC
    /\ w4coord[p] = notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                   w4vote, w4coord, decisionC, aliveC, faultyC>>

\* A participant decides according to the coordinator's broadcast.
DecideCoord(p) ==
    /\ aliveP[p]
    /\ decisionP[p] = undecided
    /\ w4coord[p] # notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = w4coord[p]]
    /\ UNCHANGED <<vote, aliveP, faultyP, sentVote,
                   w4vote, w4coord, decisionC, aliveC, faultyC>>

\* A participant crashes.
Die(p) ==
    /\ aliveP[p]
    /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
    /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decisionP, sentVote,
                   w4vote, w4coord, decisionC, aliveC, faultyC>>

Next ==
    \/ \E p \in participants : RequestVote(p)
    \/ \E p \in participants : RecvVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision(p)
    \/ DieCoordinator
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortReqTimeout(p)
    \/ \E p \in participants : DecideCoord(p)
    \/ \E p \in participants : Die(p)

Spec == Init /\ [][Next]_vars

\* No two participants disagree on the transaction outcome.
Agreement ==
    ~ \E p \in participants, q \in participants :
        /\ decisionP[p] = commit
        /\ decisionP[q] = abort

\* A commit can only happen if every participant voted yes.
CommitValidity ==
    \A p \in participants :
        decisionP[p] = commit => \A q \in participants : vote[q] = yes

\* An abort is OK only if someone voted no or someone crashed.
AbortValidity ==
    \A p \in participants :
        decisionP[p] = abort =>
            \/ \E q \in participants : vote[q] = no
            \/ \E q \in participants : faultyP[q]
            \/ faultyC

\* A participant decides at most once (committed stays committed, aborted stays aborted).
Irrevocability ==
    \A p \in participants :
        /\ (decisionP[p] = commit) ~> (decisionP[p] = commit)
        /\ (decisionP[p] = abort) ~> (decisionP[p] = abort)

\* Either everybody decides, or some participant or the coordinator crashes.
DecisionOrCrash ==
    <>(\A p \in participants : decisionP[p] # undecided) \/
        \E p \in participants : faultyP[p] \/ faultyC

====
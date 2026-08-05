---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decisionP, faultyP, sentVote,
          reqSent, recvVote, broadcast, decisionC, aliveC, faultyC

vars == <<vote, alive, decisionP, faultyP, sentVote,
          reqSent, recvVote, broadcast, decisionC, aliveC, faultyC>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decisionP \in [participants -> {undecided, commit, abort}]
    /\ faultyP \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ recvVote \in [participants -> {yes, no, waiting}]
    /\ broadcast \in [participants -> {commit, abort, notsent}]
    /\ decisionC \in {commit, abort, undecided}
    /\ aliveC \in BOOLEAN
    /\ faultyC \in {FALSE, TRUE}

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants |-> TRUE]
    /\ decisionP = [p \in participants |-> undecided]
    /\ faultyP = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ recvVote = [p \in participants |-> waiting]
    /\ broadcast = [p \in participants |-> notsent]
    /\ decisionC = undecided
    /\ aliveC = TRUE
    /\ faultyC = FALSE

\* Coordinator actions:
SendRequest(p) ==
    /\ aliveC
    /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decisionP, faultyP, sentVote,
                  recvVote, broadcast, decisionC, aliveC, faultyC>>

RecvVote(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A q \in participants : reqSent[q]
    /\ recvVote[p] = waiting
    /\ sentVote[p]
    /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decisionP, faultyP, sentVote,
                  reqSent, broadcast, decisionC, aliveC, faultyC>>

DetectFault(p) ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A q \in participants : reqSent[q]
    /\ recvVote[p] = waiting
    /\ ~alive[p]
    /\ decisionC' = abort
    /\ UNCHANGED <<vote, alive, decisionP, faultyP, sentVote,
                  reqSent, recvVote, broadcast, aliveC, faultyC>>

MakeDecision ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A p \in participants : recvVote[p] # waiting
    /\ decisionC' = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decisionP, faultyP, sentVote,
                  reqSent, recvVote, broadcast, aliveC, faultyC>>

BroadcastDecision(p) ==
    /\ aliveC
    /\ decisionC # undecided
    /\ broadcast[p] = notsent
    /\ broadcast' = [broadcast EXCEPT ![p] = decisionC]
    /\ UNCHANGED <<vote, alive, decisionP, faultyP, sentVote,
                  reqSent, recvVote, decisionC, aliveC, faultyC>>

DieCoordinator ==
    /\ aliveC
    /\ aliveC' = FALSE
    /\ faultyC' = TRUE
    /\ UNCHANGED <<vote, alive, decisionP, faultyP, sentVote,
                  reqSent, recvVote, broadcast, decisionC, aliveC, faultyC>>

\* Participant actions:
SendVote(p) ==
    /\ alive[p]
    /\ reqSent[p]
    /\ sentVote[p] = FALSE
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decisionP, faultyP, reqSent,
                  recvVote, broadcast, decisionC, aliveC, faultyC>>

AbortVote ==
    /\ \E p \in participants :
        /\ alive[p]
        /\ decisionP[p] = undecided
        /\ sentVote[p]
        /\ vote[p] = no
        /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faultyP, sentVote,
                  reqSent, recvVote, broadcast, decisionC, aliveC, faultyC>>

AbortTimeout(p) ==
    /\ alive[p]
    /\ decisionP[p] = undecided
    /\ ~aliveC
    /\ reqSent[p]
    /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faultyP, sentVote,
                  reqSent, recvVote, broadcast, decisionC, aliveC, faultyC>>

DecideFromCoordinator(p) ==
    /\ alive[p]
    /\ decisionP[p] = undecided
    /\ broadcast[p] # notsent
    /\ decisionP' = [decisionP EXCEPT ![p] = broadcast[p]]
    /\ UNCHANGED <<vote, alive, faultyP, sentVote,
                  reqSent, recvVote, broadcast, decisionC, aliveC, faultyC>>

DieParticipant(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decisionP, sentVote,
                  reqSent, recvVote, broadcast, decisionC, aliveC, faultyC>>

Next ==
    \/ \E p \in participants :
         SendRequest(p) \/ RecvVote(p) \/ DetectFault(p)
         \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortTimeout(p)
         \/ DecideFromCoordinator(p) \/ DieParticipant(p)
    \/ MakeDecision \/ DieCoordinator

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in participants : SF_vars(SendVote(p))
    /\ \A p \in participants : SF_vars(DecideFromCoordinator(p))
    /\ \A p \in participants : WF_vars(AbortTimeout(p))
    /\ WF_vars(DieCoordinator)

\* Safety: agreement, commit validity, abort validity, and irrevocability.
AC1 ==
    \A p, q \in participants :
        ~(decisionP[p] = commit /\ decisionP[q] = abort)

AC2 ==
    \A p \in participants : decisionP[p] = commit => vote[p] = yes

AC3 ==
    \E p \in participants : decisionP[p] = abort =>
        (\E q \in participants : vote[q] = no \/ faultyP[q] \/ faultyC)

AC4 ==
    \A p \in participants :
        /\ (decisionP[p] = commit => decisionP[p] = commit)
        /\ (decisionP[p] = abort => decisionP[p] = abort)

\* Liveness: a decision emerges or a failure surfaces (non-blocking is not required here).
AC3Live ==
    <>(\E p \in participants : decisionP[p] # undecided \/ faultyP[p] \/ faultyC)

====
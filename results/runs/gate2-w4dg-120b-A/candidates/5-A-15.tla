---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Participant-level state
VARIABLES vote, aliveP, decisionP, faultyP, hasSent

\* Coordinator-level state
VARIABLES reqSent, voteRec, coordSent, decisionC, aliveC, faultyC

vars == <<vote, aliveP, decisionP, faultyP, hasSent,
          reqSent, voteRec, coordSent, decisionC, aliveC, faultyC>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ decisionP \in [participants -> {undecided, commit, abort}]
    /\ faultyP \in [participants -> BOOLEAN]
    /\ hasSent \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ voteRec \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {notsent, commit, abort}]
    /\ decisionC \in {undecided, commit, abort}
    /\ aliveC \in BOOLEAN
    /\ faultyC \in BOOLEAN

\* The coordinator may broadcast to each participant independently, so each
\* participant tracks whether it has actually received the coordinator's
\* decision -- this per-participant tracking is the reason the simple broadcast
\* variant is blocking: a coordinator crash mid-broadcast leaves some participants
\* with no decision at all, so they need not decide even if they are non-faulty.
Init ==
    /\ vote = [p \in participants |-> IF (CHOOSE b \in BOOLEAN : TRUE) THEN yes ELSE no]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ decisionP = [p \in participants |-> undecided]
    /\ faultyP = [p \in participants |-> FALSE]
    /\ hasSent = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ voteRec = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ decisionC = undecided
    /\ aliveC = TRUE
    /\ faultyC = FALSE

SendRequest ==
    /\ aliveC
    /\ \E p \in participants :
         /\ ~reqSent[p]
         /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, hasSent,
                  voteRec, coordSent, decisionC, aliveC, faultyC>>

\* Vote arrival: the coordinator accepts a participant's vote if it has asked
\* for it, is waiting, and the participant has actually sent it.
ReceiveVote ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \E p \in participants :
         /\ reqSent[p]
         /\ voteRec[p] = waiting
         /\ hasSent[p]
         /\ voteRec' = [voteRec EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, hasSent,
                  reqSent, coordSent, decisionC, aliveC, faultyC>>

DetectFault ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \E p \in participants :
         /\ reqSent[p]
         /\ voteRec[p] = waiting
         /\ ~aliveP[p]
         /\ decisionC' = abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, hasSent,
                  reqSent, voteRec, coordSent, aliveC, faultyC>>

MakeDecision ==
    /\ aliveC
    /\ decisionC = undecided
    /\ \A p \in participants : voteRec[p] # waiting
    /\ decisionC' = IF \A p \in participants : voteRec[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, hasSent,
                  reqSent, voteRec, coordSent, aliveC, faultyC>>

\* Simple broadcast: the coordinator sends the decision to one participant at a
\* time, and it may be slow (but not failed) with respect to any of them.
BroadcastDecision ==
    /\ aliveC
    /\ decisionC # undecided
    /\ \E p \in participants :
         /\ coordSent[p] = notsent
         /\ coordSent' = [coordSent EXCEPT ![p] = decisionC]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, hasSent,
                  reqSent, voteRec, decisionC, aliveC, faultyC>>

DieCoordinator ==
    /\ aliveC
    /\ aliveC' = FALSE
    /\ faultyC' = TRUE
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP, hasSent,
                  reqSent, voteRec, coordSent, decisionC, faultyC>>

SendVote ==
    /\ \E p \in participants :
         /\ aliveP[p]
         /\ reqSent[p]
         /\ ~hasSent[p]
         /\ hasSent' = [hasSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, aliveP, decisionP, faultyP,
                  reqSent, voteRec, coordSent, decisionC, aliveC, faultyC>>

AbortOnNo ==
    /\ \E p \in participants :
         /\ aliveP[p]
         /\ decisionP[p] = undecided
         /\ hasSent[p]
         /\ vote[p] = no
         /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, hasSent,
                  reqSent, voteRec, coordSent, decisionC, aliveC, faultyC>>

AbortOnNoTimeout ==
    /\ \E p \in participants :
         /\ aliveP[p]
         /\ decisionP[p] = undecided
         /\ ~aliveC
         /\ reqSent[p] = FALSE
         /\ decisionP' = [decisionP EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, aliveP, faultyP, hasSent,
                  reqSent, voteRec, coordSent, decisionC, aliveC, faultyC>>

DecideFromBroadcast ==
    /\ \E p \in participants :
         /\ aliveP[p]
         /\ decisionP[p] = undecided
         /\ coordSent[p] # notsent
         /\ decisionP' = [decisionP EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<vote, aliveP, faultyP, hasSent,
                  reqSent, voteRec, coordSent, decisionC, aliveC, faultyC>>

DieParticipant ==
    /\ \E p \in participants :
         /\ aliveP[p]
         /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
         /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decisionP, hasSent,
                  reqSent, voteRec, coordSent, decisionC, aliveC, faultyC>>

Next ==
    \/ SendRequest \/ ReceiveVote \/ DetectFault \/ MakeDecision
    \/ BroadcastDecision \/ DieCoordinator
    \/ SendVote \/ AbortOnNo \/ AbortOnNoTimeout \/ DecideFromBroadcast
    \/ DieParticipant

Spec == Init /\ [][Next]_vars
        /\ WF_vars(SendRequest) /\ WF_vars(ReceiveVote) /\ WF_vars(MakeDecision)
        /\ WF_vars(BroadcastDecision) /\ WF_vars(SendVote) /\ WF_vars(DecideFromBroadcast)

\* Safety: agreement, that a commit is only possible on unanimity, that an abort
\* is explained by a no vote or a fault, and that decisions are irreversible.
Agreement ==
    \A p, q \in participants :
        (decisionP[p] = commit /\ decisionP[q] = abort) => FALSE

CommitValid ==
    \A p \in participants : decisionP[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValid ==
    \A p \in participants : decisionP[p] = abort =>
        \/ \E q \in participants : vote[q] = no
        \/ \E q \in participants : faultyP[q]
        \/ faultyC

Irrevocable ==
    \A p \in participants :
        /\ (decisionP[p] = commit) => (decisionP' [p] = commit)
        /\ (decisionP[p] = abort) => (decisionP' [p] = abort)

DecideLiveness ==
    <>(\A p \in participants : decisionP[p] # undecided) \/ (\E p \in participants : faultyP[p]) \/ faultyC

====
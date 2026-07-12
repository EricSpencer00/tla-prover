---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* -----------------------------------------------------------------
\* State variables
\* -----------------------------------------------------------------
VARIABLES vote, alive, finalDec, faulty, sentVote,
          reqSent, recvVote, sentDecision, coordDecision

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
ParticipantSet == participants

\* Decision set
DecisionSet == {commit, abort, undecided}

\* Vote set
VoteSet == {yes, no}

\* -----------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------
Init ==
    /\ vote = [p \in ParticipantSet |-> CHOOSE v \in VoteSet : v]
    /\ alive = [p \in ParticipantSet |-> TRUE]
    /\ faulty = [p \in ParticipantSet |-> FALSE]
    /\ finalDec = [p \in ParticipantSet |-> undecided]
    /\ sentVote = [p \in ParticipantSet |-> FALSE]
    /\ reqSent = [p \in ParticipantSet |-> FALSE]
    /\ recvVote = [p \in ParticipantSet |-> waiting]
    /\ sentDecision = [p \in ParticipantSet |-> notsent]
    /\ coordDecision = undecided
    /\ \* The coordinator is represented implicitly by the above vars

\* -----------------------------------------------------------------
\* Coordinator actions
\* -----------------------------------------------------------------
\* Send vote request to a participant
SendReq(p) ==
    /\ p \in ParticipantSet
    /\ \* Coordinator is alive and undecided
    /\ coordDecision = undecided
    /\ \* The coordinator has not yet sent a request to p
    /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, faulty, finalDec, sentVote,
                  recvVote, sentDecision, coordDecision>>

\* Receive vote from a participant
RecvVote(p) ==
    /\ p \in ParticipantSet
    /\ coordDecision = undecided
    /\ \* Coordinator has requested vote from p
    /\ reqSent[p]
    /\ \* Coordinator is waiting on p
    /\ recvVote[p] = waiting
    /\ \* Participant has sent its vote
    /\ sentVote[p]
    /\ \* Update the received vote
    /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, faulty, finalDec, sentVote,
                  reqSent, sentDecision, coordDecision>>

\* Detect participant fault: participant has died without sending vote
DetectFault(p) ==
    /\ p \in ParticipantSet
    /\ coordDecision = undecided
    /\ reqSent[p]
    /\ recvVote[p] = waiting
    /\ ~sentVote[p]
    /\ ~alive[p]
    /\ \* Coordinator aborts
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, faulty, finalDec, sentVote,
                  reqSent, recvVote, sentDecision>>

\* Make decision (after receiving all votes)
MakeDecision ==
    /\ coordDecision = undecided
    /\ \* All participants have sent their votes
    /\ \A p \in ParticipantSet : recvVote[p] \in VoteSet
    /\ \* If all votes are yes, commit; otherwise abort
    /\ coordDecision' = IF \A p \in ParticipantSet : recvVote[p] = yes
                            THEN commit
                            ELSE abort
    /\ UNCHANGED <<vote, alive, faulty, finalDec, sentVote,
                  reqSent, recvVote, sentDecision>>

\* Broadcast decision to a participant
BroadcastDecision(p) ==
    /\ p \in ParticipantSet
    /\ coordDecision \in {commit, abort}
    /\ sentDecision[p] = notsent
    /\ sentDecision' = [sentDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, faulty, finalDec, sentVote,
                  reqSent, recvVote, coordDecision>>

\* Coordinator crashes
CoordDie ==
    /\ coordDecision = undecided
    /\ coordDecision' = coordDecision
    /\ UNCHANGED <<vote, alive, faulty, finalDec, sentVote,
                  reqSent, recvVote, sentDecision, coordDecision>>

\* -----------------------------------------------------------------
\* Participant actions
\* -----------------------------------------------------------------
\* Send vote (after receiving request)
SendVote(p) ==
    /\ p \in ParticipantSet
    /\ alive[p]
    /\ reqSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, faulty, finalDec, reqSent,
                  recvVote, sentDecision, coordDecision>>

\* Abort due to own vote no
AbortOnVoteNo(p) ==
    /\ p \in ParticipantSet
    /\ alive[p]
    /\ finalDec[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ finalDec' = [finalDec EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote,
                  reqSent, recvVote, sentDecision, coordDecision>>

\* Abort due to timeout (coordinator dead before sending request)
AbortOnTimeout(p) ==
    /\ p \in ParticipantSet
    /\ alive[p]
    /\ finalDec[p] = undecided
    /\ ~reqSent[p]
    /\ ~alive[p]   \* coordinator is dead (modeled by lack of request)
    /\ finalDec' = [finalDec EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote,
                  reqSent, recvVote, sentDecision, coordDecision>>

\* Decide based on coordinator broadcast
DecideFromBroadcast(p) ==
    /\ p \in ParticipantSet
    /\ alive[p]
    /\ finalDec[p] = undecided
    /\ sentDecision[p] \in {commit, abort}
    /\ finalDec' = [finalDec EXCEPT ![p] = sentDecision[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote,
                  reqSent, recvVote, coordDecision>>

\* Participant crashes
ParticipantDie(p) ==
    /\ p \in ParticipantSet
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, finalDec, sentVote,
                  reqSent, recvVote, sentDecision, coordDecision>>

\* -----------------------------------------------------------------
\* Next-state relation
\* -----------------------------------------------------------------
Next ==
    \/ \E p \in ParticipantSet : SendReq(p)
    \/ \E p \in ParticipantSet : RecvVote(p)
    \/ \E p \in ParticipantSet : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in ParticipantSet : BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in ParticipantSet : SendVote(p)
    \/ \E p \in ParticipantSet : AbortOnVoteNo(p)
    \/ \E p \in ParticipantSet : AbortOnTimeout(p)
    \/ \E p \in ParticipantSet : DecideFromBroadcast(p)
    \/ \E p \in ParticipantSet : ParticipantDie(p)

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<vote, alive, faulty, finalDec, sentVote,
                     reqSent, recvVote, sentDecision, coordDecision>>

\* -----------------------------------------------------------------
\* Type invariant (ensures all variables stay within expected ranges)
\* -----------------------------------------------------------------
TypeInv ==
    /\ vote \in [ParticipantSet -> VoteSet]
    /\ alive \in [ParticipantSet -> BOOLEAN]
    /\ faulty \in [ParticipantSet -> BOOLEAN]
    /\ finalDec \in [ParticipantSet -> DecisionSet]
    /\ sentVote \in [ParticipantSet -> BOOLEAN]
    /\ reqSent \in [ParticipantSet -> BOOLEAN]
    /\ recvVote \in [ParticipantSet -> {waiting} \cup VoteSet]
    /\ sentDecision \in [ParticipantSet -> {notsent} \cup DecisionSet]
    /\ coordDecision \in DecisionSet

\* -----------------------------------------------------------------
\* Safety properties (for completeness, though not required by cfg)
\* -----------------------------------------------------------------
Agreement ==
    \A p, q \in ParticipantSet : finalDec[p] = finalDec[q]

CommitValidity ==
    \A p \in ParticipantSet :
        IF finalDec[p] = commit
        THEN \A q \in ParticipantSet : vote[q] = yes
        ELSE TRUE

AbortValidity ==
    \A p \in ParticipantSet :
        IF finalDec[p] = abort
        THEN (\E q \in ParticipantSet : vote[q] = no)
             \/ (\E q \in ParticipantSet : faulty[q])
             \/ FALSE
        ELSE TRUE

Irrevocability ==
    \A p \in ParticipantSet :
        (finalDec[p] = commit => \A q \in ParticipantSet : finalDec[q] = commit)
        /\ (finalDec[p] = abort => \A q \in ParticipantSet : finalDec[q] = abort)

\* -----------------------------------------------------------------
\* Additional assumptions (fairness)
\* -----------------------------------------------------------------
FairCoordinator ==
    WF_vars(<<vote, alive, faulty, finalDec, sentVote,
              reqSent, recvVote, sentDecision, coordDecision>>,
             MakeDecision)

FairParticipant ==
    WF_vars(<<vote, alive, faulty, finalDec, sentVote,
              reqSent, recvVote, sentDecision, coordDecision>>,
             \E p \in ParticipantSet :
                 SendVote(p) \/ AbortOnVoteNo(p) \/ AbortOnTimeout(p)
                 \/ DecideFromBroadcast(p))

\* -----------------------------------------------------------------
\* End of module
\* -----------------------------------------------------------------
====
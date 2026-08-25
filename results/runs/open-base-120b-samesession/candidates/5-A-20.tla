---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES vote,                     \* participants' votes (yes/no)
          sentVote,                 \* whether a participant has sent its vote
          decisionP,                \* participants' final decisions
          aliveP,                   \* participants' aliveness
          requestSent,              \* coordinator has sent request to p?
          voteReceived,             \* coordinator's view of p's vote
          broadcastSent,            \* decision broadcasted to p
          decisionC,                \* coordinator's decision
          coordAlive                \* coordinator aliveness

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
VoteSet      == {yes, no}
DecisionSet  == {undecided, commit, abort}
ReceivedVal  == VoteSet \cup {waiting}
BroadcastVal == DecisionSet \cup {notsent}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
   /\ vote          \in [participants -> VoteSet]
   /\ sentVote      = [p \in participants |-> FALSE]
   /\ decisionP     = [p \in participants |-> undecided]
   /\ aliveP        = [p \in participants |-> TRUE]
   /\ requestSent   = [p \in participants |-> FALSE]
   /\ voteReceived  = [p \in participants |-> waiting]
   /\ broadcastSent = [p \in participants |-> notsent]
   /\ decisionC     = undecided
   /\ coordAlive    = TRUE

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CoordSendReq ==
   \E p \in participants :
        /\ coordAlive
        /\ ~requestSent[p]
        /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED << vote, sentVote, decisionP, aliveP,
                       voteReceived, broadcastSent, decisionC, coordAlive >>

CoordReceiveVote ==
   \E p \in participants :
        /\ coordAlive
        /\ decisionC = undecided
        /\ requestSent[p]
        /\ voteReceived[p] = waiting
        /\ sentVote[p]
        /\ voteReceived' = [voteReceived EXCEPT ![p] = vote[p]]
        /\ UNCHANGED << vote, sentVote, decisionP, aliveP,
                       requestSent, broadcastSent, decisionC, coordAlive >>

CoordDetectFault ==
   \E p \in participants :
        /\ coordAlive
        /\ decisionC = undecided
        /\ requestSent[p]
        /\ voteReceived[p] = waiting
        /\ ~aliveP[p]                \* participant crashed
        /\ decisionC' = abort
        /\ UNCHANGED << vote, sentVote, decisionP, aliveP,
                       requestSent, voteReceived, broadcastSent, coordAlive >>

CoordMakeDecision ==
   /\ coordAlive
   /\ decisionC = undecided
   /\ \A p \in participants : voteReceived[p] # waiting
   /\ decisionC' = IF \A p \in participants : voteReceived[p] = yes
                      THEN commit ELSE abort
   /\ UNCHANGED << vote, sentVote, decisionP, aliveP,
                  requestSent, voteReceived, broadcastSent, coordAlive >>

CoordBroadcast ==
   \E p \in participants :
        /\ coordAlive
        /\ decisionC # undecided
        /\ broadcastSent[p] = notsent
        /\ broadcastSent' = [broadcastSent EXCEPT ![p] = decisionC]
        /\ UNCHANGED << vote, sentVote, decisionP, aliveP,
                       requestSent, voteReceived, decisionC, coordAlive >>

CoordDie ==
   /\ coordAlive
   /\ coordAlive' = FALSE
   /\ UNCHANGED << vote, sentVote, decisionP, aliveP,
                  requestSent, voteReceived, broadcastSent, decisionC >>

ParticipantSendVote ==
   \E p \in participants :
        /\ aliveP[p]
        /\ requestSent[p]
        /\ ~sentVote[p]
        /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
        /\ UNCHANGED << vote, decisionP, aliveP, requestSent,
                       voteReceived, broadcastSent, decisionC, coordAlive >>

ParticipantAbortOnVote ==
   \E p \in participants :
        /\ aliveP[p]
        /\ decisionP[p] = undecided
        /\ sentVote[p]
        /\ vote[p] = no
        /\ decisionP' = [decisionP EXCEPT ![p] = abort]
        /\ UNCHANGED << vote, sentVote, aliveP, requestSent,
                       voteReceived, broadcastSent, decisionC, coordAlive >>

ParticipantAbortOnTimeout ==
   \E p \in participants :
        /\ aliveP[p]
        /\ decisionP[p] = undecided
        /\ ~coordAlive                      \* coordinator crashed
        /\ ~requestSent[p]                  \* never got request
        /\ decisionP' = [decisionP EXCEPT ![p] = abort]
        /\ UNCHANGED << vote, sentVote, aliveP, requestSent,
                       voteReceived, broadcastSent, decisionC, coordAlive >>

ParticipantDecideFromBroadcast ==
   \E p \in participants :
        /\ aliveP[p]
        /\ decisionP[p] = undecided
        /\ broadcastSent[p] # notsent
        /\ decisionP' = [decisionP EXCEPT ![p] = broadcastSent[p]]
        /\ UNCHANGED << vote, sentVote, aliveP, requestSent,
                       voteReceived, broadcastSent, decisionC, coordAlive >>

ParticipantDie ==
   \E p \in participants :
        /\ aliveP[p]
        /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
        /\ UNCHANGED << vote, sentVote, decisionP, requestSent,
                       voteReceived, broadcastSent, decisionC, coordAlive >>

Next ==
   \/ CoordSendReq
   \/ CoordReceiveVote
   \/ CoordDetectFault
   \/ CoordMakeDecision
   \/ CoordBroadcast
   \/ CoordDie
   \/ ParticipantSendVote
   \/ ParticipantAbortOnVote
   \/ ParticipantAbortOnTimeout
   \/ ParticipantDecideFromBroadcast
   \/ ParticipantDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< vote, sentVote, decisionP, aliveP,
                     requestSent, voteReceived, broadcastSent,
                     decisionC, coordAlive >>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
   /\ vote          \in [participants -> VoteSet]
   /\ sentVote      \in [participants -> BOOLEAN]
   /\ decisionP     \in [participants -> DecisionSet]
   /\ aliveP        \in [participants -> BOOLEAN]
   /\ requestSent   \in [participants -> BOOLEAN]
   /\ voteReceived  \in [participants -> ReceivedVal]
   /\ broadcastSent \in [participants -> BroadcastVal]
   /\ decisionC     \in DecisionSet
   /\ coordAlive    \in BOOLEAN

====
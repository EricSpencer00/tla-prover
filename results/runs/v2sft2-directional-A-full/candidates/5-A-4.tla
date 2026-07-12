---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
VoteVotes == {yes, no}
Decision == {commit, abort, undecided}
Status == {alive, dead}
SendStatus == {notsent, sent}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pVote,          \* [p \in participants |-> VoteVotes]
    pStatus,        \* [p \in participants |-> Status]
    pDecision,      \* [p \in participants |-> Decision]
    pFaulty,        \* [p \in participants |-> BOOLEAN]
    pSentVote,      \* [p \in participants |-> BOOLEAN]

    cReqSent,       \* [p \in participants |-> BOOLEAN]
    cVoteRecv,      \* [p \in participants |-> VoteVotes \cup {waiting}]
    cSendStatus,    \* [p \in participants |-> SendStatus]
    cDecision,      \* Decision
    cStatus,        \* Status
    cFaulty          \* BOOLEAN

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllParticipants == participants

\* Predicate that checks whether all participants have sent a vote
AllVotesSent == \A p \in participants: pSentVote[p]

\* Predicate that checks whether all votes have been received by the coordinator
AllVotesReceived == \A p \in participants: cVoteRecv[p] \in VoteVotes

\* Predicate that checks whether the coordinator has sent its decision to all
AllDecisionsSent == \A p \in participants: cSendStatus[p] = sent

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pVote \in [participants -> VoteVotes]
       \/ pVote = [p \in participants |-> [vote \in VoteVotes: vote]]
    /\ pStatus = [p \in participants |-> alive]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ cReqSent = [p \in participants |-> FALSE]
    /\ cVoteRecv = [p \in participants |-> waiting]
    /\ cSendStatus = [p \in participants |-> notsent]
    /\ cDecision = undecided
    /\ cStatus = alive
    /\ cFaulty = FALSE

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendVoteReq(p) ==
    /\ cStatus = alive
    /\ cDecision = undecided
    /\ cReqSent[p] = FALSE
    /\ cReqSent' = [cReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pStatus, pDecision, pFaulty,
                   pSentVote, cVoteRecv, cSendStatus, cDecision,
                   cStatus, cFaulty>>

RecvVote(p) ==
    /\ cStatus = alive
    /\ cDecision = undecided
    /\ cReqSent[p] = TRUE
    /\ cVoteRecv[p] = waiting
    /\ pSentVote[p] = TRUE
    /\ cVoteRecv' = [cVoteRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pStatus, pDecision, pFaulty,
                   pSentVote, cReqSent, cSendStatus, cDecision,
                   cStatus, cFaulty>>

DetectFault(p) ==
    /\ cStatus = alive
    /\ cDecision = undecided
    /\ cReqSent[p] = TRUE
    /\ cVoteRecv[p] = waiting
    /\ pStatus[p] = dead
    /\ cDecision' = abort
    /\ cStatus' = dead
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pStatus, pDecision, pFaulty,
                   pSentVote, cReqSent, cVoteRecv, cSendStatus>>

MakeDecision ==
    /\ cStatus = alive
    /\ cDecision = undecided
    /\ AllVotesReceived
    /\ cDecision' = IF \A p \in participants: cVoteRecv[p] = yes
                    THEN commit
                    ELSE abort
    /\ cFaulty' = FALSE
    /\ UNCHANGED <<pVote, pStatus, pDecision, pFaulty,
                   pSentVote, cReqSent, cVoteRecv, cSendStatus,
                   cStatus>>

BroadcastDecision(p) ==
    /\ cStatus = alive
    /\ cDecision \in {commit, abort}
    /\ cSendStatus[p] = notsent
    /\ cSendStatus' = [cSendStatus EXCEPT ![p] = sent]
    /\ UNCHANGED <<pVote, pStatus, pDecision, pFaulty,
                   pSentVote, cReqSent, cVoteRecv, cDecision,
                   cStatus, cFaulty>>

CoordinatorDie ==
    /\ cStatus = alive
    /\ cStatus' = dead
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pStatus, pDecision, pFaulty,
                   pSentVote, cReqSent, cVoteRecv, cSendStatus,
                   cDecision>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ pStatus[p] = alive
    /\ cReqSent[p] = TRUE
    /\ pSentVote[p] = FALSE
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pStatus, pDecision, pFaulty,
                   cReqSent, cVoteRecv, cSendStatus, cDecision,
                   cStatus, cFaulty>>

AbortOnVote(p) ==
    /\ pStatus[p] = alive
    /\ pDecision[p] = undecided
    /\ pSentVote[p] = TRUE
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pStatus, pFaulty,
                   cReqSent, cVoteRecv, cSendStatus, cDecision,
                   cStatus, cFaulty>>

AbortOnTimeout(p) ==
    /\ pStatus[p] = alive
    /\ pDecision[p] = undecided
    /\ cReqSent[p] = FALSE
    /\ cStatus = dead
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pStatus, pFaulty,
                   pSentVote, cReqSent, cVoteRecv, cSendStatus,
                   cDecision, cStatus, cFaulty>>

DecideFromBroadcast(p) ==
    /\ pStatus[p] = alive
    /\ pDecision[p] = undecided
    /\ cSendStatus[p] = sent
    /\ pDecision' = [pDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<pVote, pStatus, pFaulty,
                   pSentVote, cReqSent, cVoteRecv, cSendStatus,
                   cDecision, cStatus, cFaulty>>

ParticipantDie(p) ==
    /\ pStatus[p] = alive
    /\ pStatus' = [pStatus EXCEPT ![p] = dead]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecision, pSentVote,
                   cReqSent, cVoteRecv, cSendStatus, cDecision,
                   cStatus, cFaulty>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: SendVoteReq(p)
    \/ \E p \in participants: RecvVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: BroadcastDecision(p)
    \/ CoordinatorDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pVote, pStatus, pDecision, pFaulty,
                          pSentVote, cReqSent, cVoteRecv, cSendStatus,
                          cDecision, cStatus, cFaulty>>

\* ----------------------------------------------------------------------
\* Type invariant (optional for TLC)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ pVote \in [participants -> VoteVotes]
    /\ pStatus \in [participants -> Status]
    /\ pDecision \in [participants -> Decision]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ cReqSent \in [participants -> BOOLEAN]
    /\ cVoteRecv \in [participants -> VoteVotes \cup {waiting}]
    /\ cSendStatus \in [participants -> SendStatus]
    /\ cDecision \in Decision
    /\ cStatus \in Status
    /\ cFaulty \in BOOLEAN

\* ----------------------------------------------------------------------
\* Safety invariants (optional, not required by the .cfg but useful)
\* ----------------------------------------------------------------------
AC1 == \A p, q \in participants :
          pDecision[p] = commit /\ qDecision[q] = abort => FALSE

AC2 == \A p \in participants :
          pDecision[p] = commit => \A q \in participants: pVote[q] = yes

AC3 == \A p \in participants :
          pDecision[p] = abort => (\E q \in participants: pVote[q] = no)
                                 \/ (\E q \in participants: pFaulty[q])
                                 \/ (cFaulty)

AC4 == \A p \in participants :
          pDecision[p] = commit => pDecision[p] = commit
          /\ pDecision[p] = abort => pDecision[p] = abort
          /\ pDecision[p] \in {commit, abort, undecided}
\* ----------------------------------------------------------------------
\* END OF MODULE
\* ----------------------------------------------------------------------
====
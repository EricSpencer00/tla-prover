---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Assume a non‑empty set of participants
ASSUME participants # {}

VARIABLES
    cAlive, cFaulty, cDecision, cReqSent, cVoteRecv, cBroadSent,
    pAlive, pFaulty, pVote, pSentVote, pDecision

\* Helper predicate
IsParticipant(p) == p \in participants

\* Initial state
Init ==
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cDecision = undecided
    /\ cReqSent = [p \in participants |-> FALSE]
    /\ cVoteRecv = [p \in participants |-> waiting]
    /\ cBroadSent = [p \in participants |-> notsent]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]

\* Coordinator sends a vote request to a participant
CoordSendReq(p) ==
    /\ IsParticipant(p)
    /\ cAlive
    /\ ~cReqSent[p]
    /\ cReqSent' = [cReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cVoteRecv, cBroadSent,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

\* Participant sends its vote after having received a request
ParticipantSendVote(p) ==
    /\ IsParticipant(p)
    /\ pAlive[p]
    /\ cReqSent[p]
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cVoteRecv, cBroadSent,
                  pAlive, pFaulty, pVote, pDecision>>

\* Coordinator receives a vote from a participant
CoordReceiveVote(p) ==
    /\ IsParticipant(p)
    /\ cAlive
    /\ cDecision = undecided
    /\ cReqSent[p]
    /\ cVoteRecv[p] = waiting
    /\ pSentVote[p]
    /\ cVoteRecv' = [cVoteRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cBroadSent,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

\* Coordinator detects a participant fault and aborts
CoordDetectFault(p) ==
    /\ IsParticipant(p)
    /\ cAlive
    /\ cDecision = undecided
    /\ cReqSent[p]
    /\ cVoteRecv[p] = waiting
    /\ ~pAlive[p]
    /\ ~pSentVote[p]
    /\ cDecision' = abort
    /\ UNCHANGED <<cAlive, cFaulty, cReqSent, cVoteRecv, cBroadSent,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

\* Coordinator makes a final decision after all votes are in
CoordMakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants : cVoteRecv[p] # waiting
    /\ IF \A p \in participants : cVoteRecv[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED <<cAlive, cFaulty, cReqSent, cVoteRecv, cBroadSent,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

\* Coordinator broadcasts its decision to a participant
BroadcastDecision(p) ==
    /\ IsParticipant(p)
    /\ cAlive
    /\ cDecision # undecided
    /\ cBroadSent[p] = notsent
    /\ cBroadSent' = [cBroadSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cVoteRecv,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

\* Participant adopts the coordinator's broadcast decision
ParticipantDecide(p) ==
    /\ IsParticipant(p)
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cBroadSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cBroadSent[p]]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cVoteRecv, cBroadSent,
                  pAlive, pFaulty, pVote, pSentVote>>

\* Participant aborts because its own vote is NO
ParticipantAbortOnVote(p) ==
    /\ IsParticipant(p)
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cVoteRecv, cBroadSent,
                  pAlive, pFaulty, pVote, pSentVote>>

\* Participant aborts because coordinator died before sending a request
ParticipantAbortOnTimeout(p) ==
    /\ IsParticipant(p)
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ ~cReqSent[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cVoteRecv, cBroadSent,
                  pAlive, pFaulty, pVote, pSentVote>>

\* Participant crashes
ParticipantDie(p) ==
    /\ IsParticipant(p)
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cVoteRecv, cBroadSent,
                  pVote, pSentVote, pDecision>>

\* Coordinator crashes
CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<cDecision, cReqSent, cVoteRecv, cBroadSent,
                  pAlive, pFaulty, pVote, pSentVote, pDecision>>

\* Next-state relation
Next ==
    \/ \E p \in participants : CoordSendReq(p)
    \/ \E p \in participants : ParticipantSendVote(p)
    \/ \E p \in participants : CoordReceiveVote(p)
    \/ \E p \in participants : CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants : BroadcastDecision(p)
    \/ \E p \in participants : ParticipantDecide(p)
    \/ \E p \in participants : ParticipantAbortOnVote(p)
    \/ \E p \in participants : ParticipantAbortOnTimeout(p)
    \/ \E p \in participants : ParticipantDie(p)
    \/ CoordDie

\* Tuple of all variables for stuttering steps
Vars == <<cAlive, cFaulty, cDecision, cReqSent, cVoteRecv, cBroadSent,
          pAlive, pFaulty, pVote, pSentVote, pDecision>>

\* Specification
Spec == Init /\ [][Next]_Vars

\* Type invariant
TypeInv ==
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cDecision \in {undecided, commit, abort}
    /\ cReqSent \in [participants -> BOOLEAN]
    /\ cVoteRecv \in [participants -> {waiting, yes, no}]
    /\ cBroadSent \in [participants -> {notsent, commit, abort}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {yes, no}]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]

====
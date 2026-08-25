---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences

CONSTANTS 
    participants, 
    yes, no, 
    undecided, commit, abort, 
    waiting, notsent

VARIABLES 
    cAlive, cFaulty, cDecision, 
    cReqSent, cVotes, cBroadcast, 
    pAlive, pFaulty, pVote, pSent, pDecision

\*--------------------------------------------------------------------
\* Helper definition for the set of all variables
vars == <<cAlive, cFaulty, cDecision, 
          cReqSent, cVotes, cBroadcast, 
          pAlive, pFaulty, pVote, pSent, pDecision>>

\*--------------------------------------------------------------------
\* Initial state
Init ==
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cDecision = undecided
    /\ cReqSent = [p \in participants |-> FALSE]
    /\ cVotes   = [p \in participants |-> waiting]
    /\ cBroadcast = [p \in participants |-> notsent]
    /\ pAlive   = [p \in participants |-> TRUE]
    /\ pFaulty  = [p \in participants |-> FALSE]
    /\ pVote    \in [participants -> {yes, no}]
    /\ pSent    = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]

\*--------------------------------------------------------------------
\* Coordinator actions
SendVoteReq ==
    \E p \in participants :
        /\ cAlive = TRUE
        /\ ~cReqSent[p]
        /\ cReqSent' = [cReqSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED <<cAlive, cFaulty, cDecision, cVotes, cBroadcast,
                       pAlive, pFaulty, pVote, pSent, pDecision>>

ReceiveVote ==
    \E p \in participants :
        /\ cAlive = TRUE
        /\ cDecision = undecided
        /\ cReqSent[p] = TRUE
        /\ cVotes[p] = waiting
        /\ pAlive[p] = TRUE
        /\ pSent[p] = TRUE
        /\ cVotes' = [cVotes EXCEPT ![p] = pVote[p]]
        /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cBroadcast,
                       pAlive, pFaulty, pVote, pSent, pDecision>>

DetectFault ==
    \E p \in participants :
        /\ cAlive = TRUE
        /\ cDecision = undecided
        /\ cReqSent[p] = TRUE
        /\ cVotes[p] = waiting
        /\ pAlive[p] = FALSE
        /\ cDecision' = abort
        /\ UNCHANGED <<cAlive, cFaulty, cReqSent, cVotes, cBroadcast,
                       pAlive, pFaulty, pVote, pSent, pDecision>>

MakeDecision ==
    /\ cAlive = TRUE
    /\ cDecision = undecided
    /\ \A p \in participants :
          cReqSent[p] = TRUE /\ cVotes[p] # waiting
    /\ IF \A p \in participants : cVotes[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED <<cAlive, cFaulty, cReqSent, cVotes, cBroadcast,
                   pAlive, pFaulty, pVote, pSent, pDecision>>

Broadcast ==
    \E p \in participants :
        /\ cAlive = TRUE
        /\ cDecision # undecided
        /\ cBroadcast[p] = notsent
        /\ cBroadcast' = [cBroadcast EXCEPT ![p] = cDecision]
        /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cVotes,
                       pAlive, pFaulty, pVote, pSent, pDecision>>

CoordinatorDie ==
    /\ cAlive = TRUE
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<cDecision, cReqSent, cVotes, cBroadcast,
                   pAlive, pFaulty, pVote, pSent, pDecision>>

\*--------------------------------------------------------------------
\* Participant actions
SendVote ==
    \E p \in participants :
        /\ pAlive[p] = TRUE
        /\ cReqSent[p] = TRUE
        /\ pSent[p] = FALSE
        /\ pSent' = [pSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cVotes,
                       cBroadcast, pAlive, pFaulty, pVote, pDecision>>

AbortOnVote ==
    \E p \in participants :
        /\ pAlive[p] = TRUE
        /\ pDecision[p] = undecided
        /\ pSent[p] = TRUE
        /\ pVote[p] = no
        /\ pDecision' = [pDecision EXCEPT ![p] = abort]
        /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cVotes,
                       cBroadcast, pAlive, pFaulty, pVote, pSent>>

AbortOnTimeout ==
    \E p \in participants :
        /\ pAlive[p] = TRUE
        /\ pDecision[p] = undecided
        /\ cAlive = FALSE
        /\ cReqSent[p] = FALSE
        /\ pDecision' = [pDecision EXCEPT ![p] = abort]
        /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cVotes,
                       cBroadcast, pAlive, pFaulty, pVote, pSent>>

DecideOnBroadcast ==
    \E p \in participants :
        /\ pAlive[p] = TRUE
        /\ pDecision[p] = undecided
        /\ cBroadcast[p] # notsent
        /\ pDecision' = [pDecision EXCEPT ![p] = cBroadcast[p]]
        /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cVotes,
                       cBroadcast, pAlive, pFaulty, pVote, pSent>>

ParticipantDie ==
    \E p \in participants :
        /\ pAlive[p] = TRUE
        /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
        /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
        /\ UNCHANGED <<cAlive, cFaulty, cDecision, cReqSent, cVotes,
                       cBroadcast, pVote, pSent, pDecision>>

\*--------------------------------------------------------------------
\* Combined next-state relation
Next ==
    \/ SendVoteReq
    \/ ReceiveVote
    \/ DetectFault
    \/ MakeDecision
    \/ Broadcast
    \/ CoordinatorDie
    \/ SendVote
    \/ AbortOnVote
    \/ AbortOnTimeout
    \/ DecideOnBroadcast
    \/ ParticipantDie

\*--------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\*--------------------------------------------------------------------
\* Type invariant
TypeInv ==
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cDecision \in {undecided, commit, abort}
    /\ cReqSent \in [participants -> BOOLEAN]
    /\ cVotes    \in [participants -> {yes, no, waiting}]
    /\ cBroadcast \in [participants -> {commit, abort, notsent}]
    /\ pAlive   \in [participants -> BOOLEAN]
    /\ pFaulty  \in [participants -> BOOLEAN]
    /\ pVote    \in [participants -> {yes, no}]
    /\ pSent    \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]

====
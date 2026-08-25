---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    participants, \* Set of participant identifiers
    yes, no,          \* Vote values
    undecided, commit, abort, \* Decision values
    waiting, notsent   \* Communication status values

VARIABLES
    pVote,          \* [p \in participants -> {yes,no}]
    pAlive,         \* [p \in participants -> BOOLEAN]
    pFaulty,        \* [p \in participants -> BOOLEAN]
    pSentVote,      \* [p \in participants -> BOOLEAN]
    pDecision,      \* [p \in participants -> {undecided,commit,abort}]
    cAlive,         \* BOOLEAN
    cFaulty,        \* BOOLEAN
    cSentReq,       \* [p \in participants -> BOOLEAN]   \* request sent?
    cVoteRecv,      \* [p \in participants -> {yes,no,waiting}]
    cDecision,      \* {undecided,commit,abort}
    cSentDec        \* [p \in participants -> {commit,abort,notsent}]

\* ----------------------------------------------------------------------
\* State space
\* ----------------------------------------------------------------------
vars == << pVote, pAlive, pFaulty, pSentVote, pDecision,
           cAlive, cFaulty, cSentReq, cVoteRecv, cDecision, cSentDec >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pVote      \in [participants -> {yes, no}]
    /\ pAlive     = [p \in participants |-> TRUE]
    /\ pFaulty    = [p \in participants |-> FALSE]
    /\ pSentVote  = [p \in participants |-> FALSE]
    /\ pDecision  = [p \in participants |-> undecided]
    /\ cAlive     = TRUE
    /\ cFaulty    = FALSE
    /\ cSentReq   = [p \in participants |-> FALSE]
    /\ cVoteRecv  = [p \in participants |-> waiting]
    /\ cDecision  = undecided
    /\ cSentDec   = [p \in participants |-> notsent]

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
AllRequestsSent == \A p \in participants : cSentReq[p]
AllVotesReceived == \A p \in participants : cVoteRecv[p] # waiting

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendVoteReq(p) ==
    /\ cAlive
    /\ ~cSentReq[p]
    /\ cSentReq' = [cSentReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote, pDecision,
                   cAlive, cFaulty, cVoteRecv, cDecision, cSentDec >>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ AllRequestsSent
    /\ cVoteRecv[p] = waiting
    /\ pSentVote[p]            \* participant has sent its vote
    /\ cVoteRecv' = [cVoteRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote, pDecision,
                   cAlive, cFaulty, cSentReq, cDecision, cSentDec >>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ AllRequestsSent
    /\ cVoteRecv[p] = waiting
    /\ ~pAlive[p]               \* participant has died without sending vote
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote, pDecision,
                   cAlive, cFaulty, cSentReq, cVoteRecv, cSentDec >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ AllVotesReceived
    /\ IF \A p \in participants : cVoteRecv[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote, pDecision,
                   cAlive, cFaulty, cSentReq, cVoteRecv, cSentDec >>

BroadcastDecision(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cSentDec[p] = notsent
    /\ cSentDec' = [cSentDec EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote, pDecision,
                   cAlive, cFaulty, cSentReq, cVoteRecv, cDecision >>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote, pDecision,
                   cSentReq, cVoteRecv, cDecision, cSentDec >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ pAlive[p]
    /\ cSentReq[p]                \* request already sent
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                   cAlive, cFaulty, cSentReq, cVoteRecv, cDecision, cSentDec >>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                   cAlive, cFaulty, cSentReq, cVoteRecv, cDecision, cSentDec >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive                     \* coordinator has died
    /\ ~cSentReq[p]                \* no request was ever sent
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                   cAlive, cFaulty, cSentReq, cVoteRecv, cDecision, cSentDec >>

DecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cSentDec[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cSentDec[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                   cAlive, cFaulty, cSentReq, cVoteRecv, cDecision, cSentDec >>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pSentVote, pDecision,
                   cAlive, cFaulty, cSentReq, cVoteRecv, cDecision, cSentDec >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendVoteReq(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideFromBroadcast(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ pVote      \in [participants -> {yes, no}]
    /\ pAlive     \in [participants -> BOOLEAN]
    /\ pFaulty    \in [participants -> BOOLEAN]
    /\ pSentVote  \in [participants -> BOOLEAN]
    /\ pDecision  \in [participants -> {undecided, commit, abort}]
    /\ cAlive     \in BOOLEAN
    /\ cFaulty    \in BOOLEAN
    /\ cSentReq   \in [participants -> BOOLEAN]
    /\ cVoteRecv  \in [participants -> {yes, no, waiting}]
    /\ cDecision  \in {undecided, commit, abort}
    /\ cSentDec   \in [participants -> {commit, abort, notsent}]

=============================================================================
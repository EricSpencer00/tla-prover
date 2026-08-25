---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES 
    pVote,          \* [participants -> {yes,no}]
    pAlive,         \* [participants -> BOOLEAN]
    pFaulty,        \* [participants -> BOOLEAN]
    pDecided,       \* [participants -> {undecided, commit, abort}]
    pSent,          \* [participants -> BOOLEAN]  \* has the participant sent its vote?
    cAlive,         \* BOOLEAN
    cFaulty,        \* BOOLEAN
    reqSent,        \* [participants -> BOOLEAN]  \* coordinator sent vote request?
    voteRecv,       \* [participants -> {yes,no,waiting}]
    cDecision,      \* {undecided, commit, abort}
    broadcast       \* [participants -> {notsent, commit, abort}]

\*=====================================================================
\* Helper definition of the full state vector
\*=====================================================================
vars == << pVote, pAlive, pFaulty, pDecided, pSent,
           cAlive, cFaulty, reqSent, voteRecv, cDecision, broadcast >>

\*=====================================================================
\* Initialization
\*=====================================================================
Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pDecided = [p \in participants |-> undecided]
    /\ pSent = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ reqSent = [p \in participants |-> FALSE]
    /\ voteRecv = [p \in participants |-> waiting]
    /\ cDecision = undecided
    /\ broadcast = [p \in participants |-> notsent]

\*=====================================================================
\* Coordinator actions
\*=====================================================================
SendVoteReq ==
    \E p \in participants :
        /\ cAlive /\ ~cFaulty
        /\ ~reqSent[p]
        /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED << pVote, pAlive, pFaulty, pDecided, pSent,
                       cAlive, cFaulty, voteRecv, cDecision, broadcast >>

ReceiveVote ==
    \E p \in participants :
        /\ cAlive /\ ~cFaulty /\ cDecision = undecided
        /\ reqSent[p]               \* request already sent
        /\ voteRecv[p] = waiting
        /\ pAlive[p] /\ ~pFaulty[p] /\ pSent[p]
        /\ voteRecv' = [voteRecv EXCEPT ![p] = pVote[p]]
        /\ UNCHANGED << pVote, pAlive, pFaulty, pDecided, pSent,
                       cAlive, cFaulty, reqSent, cDecision, broadcast >>

DetectFault ==
    \E p \in participants :
        /\ cAlive /\ ~cFaulty /\ cDecision = undecided
        /\ reqSent[p]
        /\ voteRecv[p] = waiting
        /\ ~pAlive[p] /\ pFaulty[p]          \* participant crashed before voting
        /\ cDecision' = abort
        /\ UNCHANGED << pVote, pAlive, pFaulty, pDecided, pSent,
                       cAlive, cFaulty, reqSent, voteRecv, broadcast >>

MakeDecision ==
    /\ cAlive /\ ~cFaulty /\ cDecision = undecided
    /\ \A p \in participants : voteRecv[p] # waiting
    /\ IF \A p \in participants : voteRecv[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecided, pSent,
                   cAlive, cFaulty, reqSent, voteRecv, broadcast >>

BroadcastDecision ==
    \E p \in participants :
        /\ cAlive /\ ~cFaulty
        /\ cDecision # undecided
        /\ broadcast[p] = notsent
        /\ broadcast' = [broadcast EXCEPT ![p] = cDecision]
        /\ UNCHANGED << pVote, pAlive, pFaulty, pDecided, pSent,
                       cAlive, cFaulty, reqSent, voteRecv, cDecision >>

CoordDie ==
    /\ cAlive /\ ~cFaulty
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecided, pSent,
                   reqSent, voteRecv, cDecision, broadcast >>

\*=====================================================================
\* Participant actions
\*=====================================================================
SendVote ==
    \E p \in participants :
        /\ pAlive[p] /\ ~pFaulty[p]
        /\ reqSent[p]               \* coordinator asked for vote
        /\ ~pSent[p]
        /\ pSent' = [pSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED << pVote, pAlive, pFaulty, pDecided,
                       cAlive, cFaulty, reqSent, voteRecv,
                       cDecision, broadcast >>

AbortOnVote ==
    \E p \in participants :
        /\ pAlive[p] /\ ~pFaulty[p]
        /\ pSent[p] /\ pVote[p] = no
        /\ pDecided[p] = undecided
        /\ pDecided' = [pDecided EXCEPT ![p] = abort]
        /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                       cAlive, cFaulty, reqSent, voteRecv,
                       cDecision, broadcast >>

AbortOnTimeout ==
    \E p \in participants :
        /\ pAlive[p] /\ ~pFaulty[p]
        /\ pDecided[p] = undecided
        /\ ~cAlive /\ ~cFaulty          \* coordinator crashed before sending request
        /\ pDecided' = [pDecided EXCEPT ![p] = abort]
        /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                       cAlive, cFaulty, reqSent, voteRecv,
                       cDecision, broadcast >>

DecideOnBroadcast ==
    \E p \in participants :
        /\ pAlive[p] /\ ~pFaulty[p]
        /\ pDecided[p] = undecided
        /\ broadcast[p] # notsent
        /\ pDecided' = [pDecided EXCEPT ![p] = broadcast[p]]
        /\ UNCHANGED << pVote, pAlive, pFaulty, pSent,
                       cAlive, cFaulty, reqSent, voteRecv,
                       cDecision, broadcast >>

ParticipantDie ==
    \E p \in participants :
        /\ pAlive[p] /\ ~pFaulty[p]
        /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
        /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
        /\ UNCHANGED << pVote, pDecided, pSent,
                       cAlive, cFaulty, reqSent, voteRecv,
                       cDecision, broadcast >>

\*=====================================================================
\* Next-state relation
\*=====================================================================
Next ==
    \/ SendVoteReq
    \/ ReceiveVote
    \/ DetectFault
    \/ MakeDecision
    \/ BroadcastDecision
    \/ CoordDie
    \/ SendVote
    \/ AbortOnVote
    \/ AbortOnTimeout
    \/ DecideOnBroadcast
    \/ ParticipantDie

\*=====================================================================
\* Specification
\*=====================================================================
Spec == Init /\ [][Next]_vars

\*=====================================================================
\* Type invariant (safety)
\*=====================================================================
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecided \in [participants -> {undecided, commit, abort}]
    /\ pSent \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ reqSent \in [participants -> BOOLEAN]
    /\ voteRecv \in [participants -> {yes, no, waiting}]
    /\ cDecision \in {undecided, commit, abort}
    /\ broadcast \in [participants -> {notsent, commit, abort}]

====
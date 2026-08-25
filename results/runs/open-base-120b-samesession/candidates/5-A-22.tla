---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    participants, \* set of participants
    yes, no,      \* possible votes
    undecided, commit, abort,   \* decisions
    waiting, notsent           \* communication markers

VARIABLES 
    pVote,          \* [participants -> {yes,no}]
    pAlive,         \* [participants -> BOOLEAN]
    pFaulty,        \* [participants -> BOOLEAN]
    pDecision,      \* [participants -> {undecided,commit,abort}]
    pSent,          \* [participants -> BOOLEAN]  \* participant has sent its vote
    cAlive,         \* BOOLEAN
    cFaulty,        \* BOOLEAN
    reqSent,        \* [participants -> BOOLEAN]  \* coordinator has sent request
    voteRecv,       \* [participants -> {yes,no,waiting}]
    cDecision,      \* {undecided,commit,abort}
    broadcastSent   \* [participants -> BOOLEAN]  \* coordinator has broadcast decision

\*=====================================================================
\* Type invariant
\*=====================================================================
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSent \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ reqSent \in [participants -> BOOLEAN]
    /\ voteRecv \in [participants -> {yes, no, waiting}]
    /\ cDecision \in {undecided, commit, abort}
    /\ broadcastSent \in [participants -> BOOLEAN]

\*=====================================================================
\* Initial state
\*=====================================================================
Init ==
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote \in [participants -> {yes, no}]   \* nondeterministic vote assignment
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSent = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ reqSent = [p \in participants |-> FALSE]
    /\ voteRecv = [p \in participants |-> waiting]
    /\ cDecision = undecided
    /\ broadcastSent = [p \in participants |-> FALSE]

\*=====================================================================
\* Coordinator actions
\*=====================================================================
SendReq(p) ==
    /\ cAlive
    /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision, pSent,
                  voteRecv, cDecision, broadcastSent, cAlive, cFaulty>>

RecvVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ reqSent[p]
    /\ voteRecv[p] = waiting
    /\ pSent[p]               \* participant has already sent its vote
    /\ voteRecv' = [voteRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision, pSent,
                  reqSent, cDecision, broadcastSent, cAlive, cFaulty>>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ reqSent[p]
    /\ voteRecv[p] = waiting
    /\ ~pAlive[p]            \* participant crashed before sending vote
    /\ cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision, pSent,
                  reqSent, voteRecv, broadcastSent, cAlive, cFaulty>>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: voteRecv[p] # waiting   \* all votes are in
    /\ IF \A p \in participants: voteRecv[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision, pSent,
                  reqSent, voteRecv, broadcastSent, cAlive, cFaulty>>

Broadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ ~broadcastSent[p]
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision, pSent,
                  reqSent, voteRecv, cDecision, cAlive, cFaulty>>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision, pSent,
                  reqSent, voteRecv, cDecision, broadcastSent>>

\*=====================================================================
\* Participant actions
\*=====================================================================
SendVote(p) ==
    /\ pAlive[p]
    /\ reqSent[p]
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pDecision,
                  reqSent, voteRecv, cDecision, cAlive, cFaulty,
                  broadcastSent>>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                  reqSent, voteRecv, cDecision, cAlive, cFaulty,
                  broadcastSent>>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive               \* coordinator crashed
    /\ ~reqSent[p]           \* never received a request
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                  reqSent, voteRecv, cDecision, cAlive, cFaulty,
                  broadcastSent>>

DecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ broadcastSent[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                  reqSent, voteRecv, cDecision, cAlive, cFaulty,
                  broadcastSent>>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecision, pSent,
                  reqSent, voteRecv, cDecision, cAlive, cFaulty,
                  broadcastSent>>

\*=====================================================================
\* Next-state relation
\*=====================================================================
Next ==
    \/ \E p \in participants: SendReq(p)
    \/ \E p \in participants: RecvVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)

\*=====================================================================
\* Specification
\*=====================================================================
vars == <<pVote, pAlive, pFaulty, pDecision, pSent,
          cAlive, cFaulty, reqSent, voteRecv, cDecision, broadcastSent>>

Spec == Init /\ [][Next]_vars

\*=====================================================================
\* Invariants
\*=====================================================================
INVARIANTS == TypeInv

====
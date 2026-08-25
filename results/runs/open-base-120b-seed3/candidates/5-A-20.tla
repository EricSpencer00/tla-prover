---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    participants, \* set of participant identifiers
    yes, no,        \* possible votes
    undecided, commit, abort,   \* decision values
    waiting, notsent            \* communication status values

VARIABLES
    pVote,          \* [participants -> {yes,no}]
    pAlive,         \* [participants -> BOOLEAN]
    pDecision,      \* [participants -> {undecided, commit, abort}]
    pSent,          \* [participants -> BOOLEAN]   \* has participant sent its vote?
    pFaulty,        \* [participants -> BOOLEAN]

    cAlive,         \* BOOLEAN
    cFaulty,        \* BOOLEAN
    reqSent,        \* [participants -> BOOLEAN]   \* has coordinator sent request?
    recvVote,       \* [participants -> {yes,no,waiting}]
    broadcastSent,  \* [participants -> BOOLEAN]   \* has coordinator broadcast decision?
    cDecision       \* {undecided, commit, abort}

\*=====================================================================
\*   Type invariant
\*=====================================================================
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSent \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]

    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ reqSent \in [participants -> BOOLEAN]
    /\ recvVote \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \in [participants -> BOOLEAN]
    /\ cDecision \in {undecided, commit, abort}

\*=====================================================================
\*   Initial state
\*=====================================================================
Init ==
    /\ pVote \in [participants -> {yes, no}]          \* nondeterministic vote
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSent = [p \in participants |-> FALSE]
    /\ pFaulty = [p \in participants |-> FALSE]

    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ reqSent = [p \in participants |-> FALSE]
    /\ recvVote = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> FALSE]
    /\ cDecision = undecided

\*=====================================================================
\*   Coordinator actions
\*=====================================================================
SendVoteRequest(p) ==
    /\ cAlive
    /\ ~reqSent[p]
    /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent, pFaulty,
                   cFaulty, recvVote, broadcastSent, cDecision >>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ reqSent[p]                     \* request already sent
    /\ recvVote[p] = waiting
    /\ pSent[p]                       \* participant has already sent vote
    /\ recvVote' = [recvVote EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent, pFaulty,
                   cAlive, cFaulty, reqSent, broadcastSent, cDecision >>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ reqSent[p]
    /\ recvVote[p] = waiting
    /\ ~pAlive[p]                     \* participant died before sending vote
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent, pFaulty,
                   cAlive, cFaulty, reqSent, recvVote, broadcastSent >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A q \in participants: recvVote[q] # waiting
    /\ IF \A q \in participants: recvVote[q] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent, pFaulty,
                   cAlive, cFaulty, reqSent, recvVote, broadcastSent >>

BroadcastDecision(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ ~broadcastSent[p]
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent, pFaulty,
                   cAlive, cFaulty, reqSent, recvVote, cDecision >>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pVote, pAlive, pDecision, pSent, pFaulty,
                   reqSent, recvVote, broadcastSent, cDecision >>

\*=====================================================================
\*   Participant actions
\*=====================================================================
ParticipantSendVote(p) ==
    /\ pAlive[p]
    /\ reqSent[p]                 \* request received
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pDecision, pFaulty,
                   cAlive, cFaulty, reqSent, recvVote, broadcastSent, cDecision >>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pSent, pFaulty,
                   cAlive, cFaulty, reqSent, recvVote, broadcastSent, cDecision >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive                     \* coordinator died
    /\ ~reqSent[p]                 \* no request ever arrived
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pSent, pFaulty,
                   cAlive, cFaulty, reqSent, recvVote, broadcastSent, cDecision >>

DecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ broadcastSent[p]            \* coordinator has sent decision
    /\ pDecision' = [pDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pSent, pFaulty,
                   cAlive, cFaulty, reqSent, recvVote, broadcastSent, cDecision >>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pDecision, pSent,
                   cAlive, cFaulty, reqSent, recvVote, broadcastSent, cDecision >>

\*=====================================================================
\*   Composite next-state relation
\*=====================================================================
Next ==
    \/ \E p \in participants: SendVoteRequest(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ \E p \in participants: BroadcastDecision(p)
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: ParticipantDie(p)
    \/ MakeDecision
    \/ CoordDie

\*=====================================================================
\*   Fairness (weak fairness on progress actions, excluding deaths)
\*=====================================================================
ParticipantProgress ==
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)

CoordinatorProgress ==
    \/ \E p \in participants: SendVoteRequest(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ \E p \in participants: BroadcastDecision(p)
    \/ MakeDecision

\*=====================================================================
\*   Specification
\*=====================================================================
Spec ==
    Init /\ [][Next]_<< pVote, pAlive, pDecision, pSent, pFaulty,
                cAlive, cFaulty, reqSent, recvVote, broadcastSent, cDecision >>
          /\ WF_<< pVote, pAlive, pDecision, pSent, pFaulty,
                cAlive, cFaulty, reqSent, recvVote, broadcastSent, cDecision >> (ParticipantProgress)
          /\ WF_<< pVote, pAlive, pDecision, pSent, pFaulty,
                cAlive, cFaulty, reqSent, recvVote, broadcastSent, cDecision >> (CoordinatorProgress)

\*=====================================================================
\*   Invariants
\*=====================================================================
THEOREM TypeInvIsInvariant == Spec => []TypeInv

\* Exported identifiers required by the .cfg file
INVARIANTS == TypeInv

====
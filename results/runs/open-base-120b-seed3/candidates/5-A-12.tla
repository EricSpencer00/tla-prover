---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State Variables
\* ----------------------------------------------------------------------
VARIABLES
    vote,               \* [p \in participants -> {yes,no}]
    pAlive,             \* [p \in participants -> BOOLEAN]  (TRUE = alive)
    pDec,               \* [p \in participants -> {undecided,commit,abort}]
    sentVote,           \* [p \in participants -> BOOLEAN]  (TRUE = vote sent)

    cAlive,             \* BOOLEAN  (coordinator alive)
    cFaulty,            \* BOOLEAN  (coordinator crashed)
    requestSent,        \* [p \in participants -> BOOLEAN]  (vote request sent)
    voteReceived,       \* [p \in participants -> {yes,no,waiting}]
    cDec,               \* {undecided,commit,abort}
    broadcastSent       \* [p \in participants -> BOOLEAN]  (decision broadcast sent)

vars == << vote, pAlive, pDec, sentVote,
           cAlive, cFaulty, requestSent, voteReceived, cDec, broadcastSent >>

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
AllRequested == \A p \in participants : requestSent[p]

AllVotesReceived == \A p \in participants : voteReceived[p] # waiting

AllDecided == \A p \in participants : pDec[p] # undecided

\* ----------------------------------------------------------------------
\* Initial State
\* ----------------------------------------------------------------------
Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDec   = [p \in participants |-> undecided]
    /\ sentVote = [p \in participants |-> FALSE]

    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ requestSent = [p \in participants |-> FALSE]
    /\ voteReceived = [p \in participants |-> waiting]
    /\ cDec = undecided
    /\ broadcastSent = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Coordinator Actions
\* ----------------------------------------------------------------------
SendVoteRequest(p) ==
    /\ cAlive
    /\ ~cFaulty
    /\ ~requestSent[p]
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, pAlive, pDec, sentVote,
                    cFaulty, voteReceived, cDec, broadcastSent >>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDec = undecided
    /\ AllRequested
    /\ voteReceived[p] = waiting
    /\ sentVote[p]            \* participant has sent its vote
    /\ voteReceived' = [voteReceived EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, pAlive, pDec, sentVote,
                    cAlive, cFaulty, requestSent, cDec, broadcastSent >>

DetectFault(p) ==
    /\ cAlive
    /\ cDec = undecided
    /\ AllRequested
    /\ voteReceived[p] = waiting
    /\ ~pAlive[p]               \* participant dead
    /\ ~sentVote[p]             \* and did not send a vote
    /\ cDec' = abort
    /\ UNCHANGED << vote, pAlive, pDec, sentVote,
                    cAlive, cFaulty, requestSent, voteReceived,
                    broadcastSent >>

MakeDecision ==
    /\ cAlive
    /\ cDec = undecided
    /\ AllRequested
    /\ AllVotesReceived
    /\ IF \A p \in participants : voteReceived[p] = yes
          THEN cDec' = commit
          ELSE cDec' = abort
    /\ UNCHANGED << vote, pAlive, pDec, sentVote,
                    cAlive, cFaulty, requestSent, voteReceived,
                    broadcastSent >>

BroadcastDecision(p) ==
    /\ cAlive
    /\ cDec # undecided
    /\ ~broadcastSent[p]
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, pAlive, pDec, sentVote,
                    cAlive, cFaulty, requestSent, voteReceived, cDec >>

CoordDie ==
    /\ cAlive
    /\ ~cFaulty
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << vote, pAlive, pDec, sentVote,
                    requestSent, voteReceived, cDec, broadcastSent >>

\* ----------------------------------------------------------------------
\* Participant Actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ pAlive[p]
    /\ requestSent[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, pAlive, pDec,
                    cAlive, cFaulty, requestSent, voteReceived,
                    cDec, broadcastSent >>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDec[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ pDec' = [pDec EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, pAlive, sentVote,
                    cAlive, cFaulty, requestSent, voteReceived,
                    cDec, broadcastSent >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDec[p] = undecided
    /\ ~cAlive                \* coordinator has died
    /\ ~requestSent[p]        \* no vote request ever arrived
    /\ pDec' = [pDec EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, pAlive, sentVote,
                    cAlive, cFaulty, requestSent, voteReceived,
                    cDec, broadcastSent >>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDec[p] = undecided
    /\ broadcastSent[p]
    /\ pDec' = [pDec EXCEPT ![p] = cDec]
    /\ UNCHANGED << vote, pAlive, sentVote,
                    cAlive, cFaulty, requestSent, voteReceived,
                    cDec, broadcastSent >>

PartDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << vote, pDec, sentVote,
                    cAlive, cFaulty, requestSent, voteReceived,
                    cDec, broadcastSent >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants :
          SendVoteRequest(p)
    \/ \E p \in participants :
          ReceiveVote(p)
    \/ \E p \in participants :
          DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants :
          BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants :
          SendVote(p)
    \/ \E p \in participants :
          AbortOnVote(p)
    \/ \E p \in participants :
          AbortOnTimeout(p)
    \/ \E p \in participants :
          DecideOnBroadcast(p)
    \/ \E p \in participants :
          PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type Invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDec   \in [participants -> {undecided, commit, abort}]
    /\ sentVote \in [participants -> BOOLEAN]

    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ requestSent \in [participants -> BOOLEAN]
    /\ voteReceived \in [participants -> {yes, no, waiting}]
    /\ cDec \in {undecided, commit, abort}
    /\ broadcastSent \in [participants -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Theorem: Spec implies TypeInv is always true
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInv

====
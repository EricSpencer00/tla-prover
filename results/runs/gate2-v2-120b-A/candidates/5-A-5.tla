---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    participants, \* the set of participant identifiers
    yes, no,           \* possible votes
    undecided, commit, abort, \* decision values
    waiting, notsent   \* special markers for votes and broadcasts

\* ----------------------------------------------------------------------
\* Helper definitions
VoteSet == {yes, no}
DecisionSet == {undecided, commit, abort}
MarkSet == {waiting, notsent}
\* ----------------------------------------------------------------------
\* Variables
VARIABLES
    pVoted,       \* [p \in participants |-> BOOLEAN]   true iff participant p has sent its vote
    pAlive,       \* [p \in participants |-> BOOLEAN]   true iff p is alive (not faulty)
    pDecision,   \* [p \in participants |-> DecisionSet]  participant's final decision
    pVote,        \* [p \in participants |-> VoteSet]       the vote chosen by p (yes/no)

    cAlive,       \* BOOLEAN indicating coordinator is alive
    cFaulty,      \* BOOLEAN indicating coordinator has crashed
    cReq,         \* [p \in participants |-> BOOLEAN]   true iff vote request sent to p
    cRecv,        \* [p \in participants |-> (VoteSet \cup {waiting})] vote received from p
    cDecision,    \* DecisionSet \cup {undecided}   coordinator's decision
    cSent         \* [p \in participants |-> (DecisionSet \cup {notsent})] broadcast status per participant

\* ----------------------------------------------------------------------
\* Initialization
Init ==
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pVoted = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pVote = [p \in participants |-> CHOOSE v \in VoteSet : TRUE]  \* nondet yes/no
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cReq = [p \in participants |-> FALSE]
    /\ cRecv = [p \in participants |-> waiting]
    /\ cDecision = undecided
    /\ cSent = [p \in participants |-> notsent]

\* ----------------------------------------------------------------------
\* Coordinator actions
CoordSendReq(p) ==
    /\ cAlive
    /\ ~cReq[p]
    /\ cReq' = [cReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cFaulty, cRecv, cDecision, cSent,
                   pAlive, pVoted, pDecision, pVote>>

CoordReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cReq[p]               \* request already sent
    /\ cRecv[p] = waiting
    /\ pVoted[p] = TRUE
    /\ cRecv' = [cRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<cAlive, cFaulty, cReq, cDecision, cSent,
                   pAlive, pVoted, pDecision, pVote>>

CoordDetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cReq[p]
    /\ cRecv[p] = waiting
    /\ ~pAlive[p]            \* participant died before sending vote
    /\ cDecision' = abort
    /\ UNCHANGED <<cAlive, cFaulty, cReq, cRecv, cSent,
                   pAlive, pVoted, pDecision, pVote>>

CoordMakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A q \in participants: cRecv[q] # waiting   \* all votes received
    /\ IF \A q \in participants: cRecv[q] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED <<cAlive, cFaulty, cReq, cRecv, cSent,
                   pAlive, pVoted, pDecision, pVote>>

CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cSent[p] = notsent
    /\ cSent' = [cSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<cAlive, cFaulty, cReq, cRecv, cDecision,
                   pAlive, pVoted, pDecision, pVote>>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<cReq, cRecv, cDecision, cSent,
                   pAlive, pVoted, pDecision, pVote>>

\* ----------------------------------------------------------------------
\* Participant actions
PartSendVote(p) ==
    /\ pAlive[p]
    /\ ~pVoted[p]
    /\ cReq[p]                \* vote request received
    /\ pVoted' = [pVoted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pAlive, pDecision, pVote,
                   cAlive, cFaulty, cReq, cRecv, cDecision, cSent>>

PartAbortOnNo(p) ==
    /\ pAlive[p]
    /\ pVoted[p]
    /\ pVote[p] = no
    /\ pDecision[p] = undecided
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pAlive, pVoted, pVote,
                   cAlive, cFaulty, cReq, cRecv, cDecision, cSent>>

PartAbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive                \* coordinator died before sending request
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pAlive, pVoted, pVote,
                   cAlive, cFaulty, cReq, cRecv, cDecision, cSent>>

PartDecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cSent[p]]
    /\ UNCHANGED <<pAlive, pVoted, pVote,
                   cAlive, cFaulty, cReq, cRecv, cDecision, cSent>>

PartDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<pVoted, pDecision, pVote,
                   cAlive, cFaulty, cReq, cRecv, cDecision, cSent>>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnNo(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<pAlive, pVoted, pDecision, pVote,
                     cAlive, cFaulty, cReq, cRecv, cDecision, cSent>>

\* ----------------------------------------------------------------------
\* Safety invariant (Agreement/Consistency)
AC1 == \A p, q \in participants :
          (pDecision[p] = commit) => (pDecision[q] = commit)

TypeInv ==
    /\ \A p \in participants:
          /\ pAlive[p] \in BOOLEAN
          /\ pVoted[p] \in BOOLEAN
          /\ pDecision[p] \in DecisionSet
          /\ pVote[p] \in VoteSet
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cReq \in [participants -> BOOLEAN]
    /\ cRecv \in [participants -> (VoteSet \cup {waiting})]
    /\ cDecision \in DecisionSet
    /\ cSent \in [participants -> (DecisionSet \cup {notsent})]

\* ----------------------------------------------------------------------
\* The name expected by the .cfg file
INVARIANT == AC1

====
---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pVote,          \* [participants -> {yes,no}]
          pAlive,         \* [participants -> BOOLEAN]
          pFaulty,        \* [participants -> BOOLEAN]
          pDecision,      \* [participants -> {undecided,commit,abort}]
          pSentVote,      \* [participants -> BOOLEAN]
          cRequested,     \* SUBSET participants
          cRecvVote,      \* [participants -> {yes,no,waiting}]
          cBroadcast,     \* [participants -> {commit,abort,notsent}]
          cDecision,      \* {undecided,commit,abort}
          cAlive,         \* BOOLEAN
          cFaulty         \* BOOLEAN

vars == << pVote, pAlive, pFaulty, pDecision, pSentVote,
           cRequested, cRecvVote, cBroadcast,
           cDecision, cAlive, cFaulty >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ cRequested = {}
    /\ cRecvVote = [p \in participants |-> waiting]
    /\ cBroadcast = [p \in participants |-> notsent]
    /\ cDecision = undecided
    /\ cAlive = TRUE
    /\ cFaulty = FALSE

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ cAlive
    /\ p \notin cRequested
    /\ cRequested' = cRequested \cup {p}
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    pSentVote, cRecvVote, cBroadcast,
                    cDecision, cFaulty >>

CoordReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in cRequested
    /\ cRecvVote[p] = waiting
    /\ pSentVote[p] = TRUE
    /\ cRecvVote' = [cRecvVote EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    pSentVote, cRequested, cBroadcast,
                    cDecision, cAlive, cFaulty >>

CoordDetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ p \in cRequested
    /\ cRecvVote[p] = waiting
    /\ pAlive[p] = FALSE
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    pSentVote, cRequested, cRecvVote,
                    cBroadcast, cAlive, cFaulty >>

CoordMakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A q \in cRequested: cRecvVote[q] # waiting
    /\ IF \A q \in cRequested: cRecvVote[q] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    pSentVote, cRequested, cRecvVote,
                    cBroadcast, cAlive, cFaulty >>

CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cBroadcast[p] = notsent
    /\ cBroadcast' = [cBroadcast EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    pSentVote, cRequested, cRecvVote,
                    cDecision, cAlive, cFaulty >>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    pSentVote, cRequested, cRecvVote,
                    cBroadcast, cDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ pAlive[p] = TRUE
    /\ pSentVote[p] = FALSE
    /\ p \in cRequested
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    cRequested, cRecvVote, cBroadcast,
                    cDecision, cAlive, cFaulty >>

PartAbortOnVote(p) ==
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ pSentVote[p] = TRUE
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                    cRequested, cRecvVote, cBroadcast,
                    cDecision, cAlive, cFaulty >>

PartAbortOnTimeout(p) ==
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ cAlive = FALSE
    /\ p \notin cRequested
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                    cRequested, cRecvVote, cBroadcast,
                    cDecision, cAlive, cFaulty >>

PartDecideFromBroadcast(p) ==
    /\ pAlive[p] = TRUE
    /\ pDecision[p] = undecided
    /\ cBroadcast[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cBroadcast[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                    cRequested, cRecvVote, cBroadcast,
                    cDecision, cAlive, cFaulty >>

PartDie(p) ==
    /\ pAlive[p] = TRUE
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pDecision, pSentVote,
                    cRequested, cRecvVote, cBroadcast,
                    cDecision, cAlive, cFaulty >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnVote(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ cRequested \subseteq participants
    /\ cRecvVote \in [participants -> {yes, no, waiting}]
    /\ cBroadcast \in [participants -> {commit, abort, notsent}]
    /\ cDecision \in {undecided, commit, abort}
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN

\* ----------------------------------------------------------------------
\* Safety properties (invariants)
\* ----------------------------------------------------------------------
AC1 == \A p,q \in participants:
          ~(pDecision[p] = commit /\ pDecision[q] = abort)

AC2 == \A p \in participants:
          (pDecision[p] = commit) => \A q \in participants: pVote[q] = yes

AC3 == \A p \in participants:
          (pDecision[p] = abort) =>
            \/ \E q \in participants: pVote[q] = no
            \/ \E q \in participants: pFaulty[q] = TRUE
            \/ cFaulty = TRUE

AC4 == \A p \in participants:
          \A d \in {commit, abort}:
            (pDecision[p] = d) => [] (pDecision[p] = d)

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
AC3Live == <> ( \A p \in participants: pDecision[p] # undecided
                \/ \E q \in participants: pFaulty[q] = TRUE
                \/ cFaulty = TRUE )

=============================================================================
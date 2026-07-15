---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    participants,   \* Set of all participant identifiers
    yes, no,        \* Vote values
    undecided, commit, abort,   \* Final decision values
    waiting, notsent \* Communication status values

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pVote,          \* [p \in participants -> {yes,no}]: the vote chosen by each participant
    pAlive,         \* [p \in participants -> BOOLEAN]: true iff participant is alive
    pDecision,      \* [p \in participants -> {undecided, commit, abort}]
    pSentVote,      \* [p \in participants -> BOOLEAN]: true iff participant has sent its vote
    cAlive,         \* BOOLEAN: true iff coordinator is alive
    cDecision,      \* {undecided, commit, abort}
    cRequested,     \* [p \in participants -> BOOLEAN]: true iff vote request has been sent to p
    cReceived,      \* [p \in participants -> {yes,no,waiting}]
    cSentDecision   \* [p \in participants -> {commit,abort,notsent}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Participants == participants

Votes == {yes, no}
Decisions == {undecided, commit, abort}
CommStatus == {waiting, notsent}
SentDecisions == {commit, abort, notsent}

\* ----------------------------------------------------------------------
\* Type invariant (for sanity checking)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pVote \in [participants -> Votes]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> Decisions]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cDecision \in Decisions
    /\ cRequested \in [participants -> BOOLEAN]
    /\ cReceived \in [participants -> {yes, no, waiting}]
    /\ cSentDecision \in [participants -> SentDecisions]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pVote = [p \in participants |-> IF Random() % 2 = 0 THEN yes ELSE no]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cDecision = undecided
    /\ cRequested = [p \in participants |-> FALSE]
    /\ cReceived = [p \in participants |-> waiting]
    /\ cSentDecision = [p \in participants |-> notsent]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CoordSendRequest(p) ==
    /\ cAlive
    /\ ~cRequested[p]
    /\ cRequested' = [cRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cDecision, cReceived, cSentDecision,
                    pVote, pAlive, pDecision, pSentVote>>

CoordRecvVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]
    /\ cReceived[p] = waiting
    /\ pSentVote[p]
    /\ cReceived' = [cReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<cAlive, cDecision, cRequested, cSentDecision,
                    pVote, pAlive, pDecision, pSentVote>>

CoordDetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]
    /\ cReceived[p] = waiting
    /\ ~pAlive[p]
    /\ cDecision' = abort
    /\ UNCHANGED <<cAlive, cRequested, cReceived, cSentDecision,
                    pVote, pAlive, pDecision, pSentVote>>

CoordMakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: cReceived[p] # waiting
    /\ IF \A p \in participants: cReceived[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED <<cAlive, cRequested, cReceived, cSentDecision,
                    pVote, pAlive, pDecision, pSentVote>>

CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cSentDecision[p] = notsent
    /\ cSentDecision' = [cSentDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<cAlive, cDecision, cRequested, cReceived,
                    pVote, pAlive, pDecision, pSentVote>>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ UNCHANGED <<cDecision, cRequested, cReceived, cSentDecision,
                    pVote, pAlive, pDecision, pSentVote>>

PartSendVote(p) ==
    /\ pAlive[p]
    /\ cRequested[p]
    /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cDecision, cRequested, cReceived,
                    cSentDecision, pVote, pAlive, pDecision>>

PartAbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSentVote[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<cAlive, cDecision, cRequested, cReceived,
                    cSentDecision, pVote, pAlive, pSentVote>>

PartAbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ ~cRequested[p]   \* coordinator never sent request to this participant
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<cAlive, cDecision, cRequested, cReceived,
                    cSentDecision, pVote, pAlive, pSentVote>>

PartDecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cSentDecision[p] \in {commit, abort}
    /\ pDecision' = [pDecision EXCEPT ![p] = cSentDecision[p]]
    /\ UNCHANGED <<cAlive, cDecision, cRequested, cReceived,
                    cSentDecision, pVote, pAlive, pSentVote>>

PartDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<cAlive, cDecision, cRequested, cReceived,
                    cSentDecision, pVote, pDecision, pSentVote>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants: CoordSendRequest(p)
    \/ \E p \in participants: CoordRecvVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: PartSendVote(p)
    \/ \E p \in participants: PartAbortOnVote(p)
    \/ \E p \in participants: PartAbortOnTimeout(p)
    \/ \E p \in participants: PartDecideFromBroadcast(p)
    \/ \E p \in participants: PartDie(p)

Spec == Init /\ [][Next]_<<pVote, pAlive, pDecision, pSentVote,
                         cAlive, cDecision, cRequested,
                         cReceived, cSentDecision>>

\* ----------------------------------------------------------------------
\* Safety invariants (optional, but useful for understanding)
\* ----------------------------------------------------------------------
Agreement ==
    \A p, q \in participants :
        (pDecision[p] = commit) => (pDecision[q] = commit)

CommitValidity ==
    \A p \in participants :
        (pDecision[p] = commit) => \A q \in participants : pVote[q] = yes

AbortValidity ==
    \A p \in participants :
        (pDecision[p] = abort) =>
            \/ \E q \in participants : pVote[q] = no
            \/ \E q \in participants : ~pAlive[q]
            \/ ~cAlive

Irrevocability ==
    \A p \in participants :
        (pDecision[p] = commit => [] (pDecision[p] = commit)) /\
        (pDecision[p] = abort  => [] (pDecision[p] = abort))

\* The only invariant required by the .cfg file
TypeInv == TypeOK

=============================================================================
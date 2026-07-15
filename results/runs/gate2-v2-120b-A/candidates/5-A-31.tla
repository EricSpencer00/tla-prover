---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

CONSTANTS
    participants,   \* Set of participant identifiers
    yes, no,         \* Vote values
    undecided, commit, abort,  \* Decision values
    waiting, notsent   \* Special markers for votes and broadcasts

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pVote,          \* [p \in participants] -> yes | no
    pAlive,         \* [p \in participants] -> BOOLEAN
    pDecision,      \* [p \in participants] -> {undecided, commit, abort}
    pSent,          \* [p \in participants] -> BOOLEAN

    cAlive,         \* BOOLEAN
    cDecision,      \* {undecided, commit, abort}
    cReq,           \* [p \in participants] -> BOOLEAN
    cRecv,          \* [p \in participants] -> {waiting} \cup {yes, no}
    cSent           \* [p \in participants] -> {notsent} \cup {commit, abort}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllSet(s) == \A x \in s : TRUE

\* Initial state
Init ==
    /\ pVote = [p \in participants |-> IF RandomElement({yes, no}) = 1 THEN yes ELSE no]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSent = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cDecision = undecided
    /\ cReq = [p \in participants |-> FALSE]
    /\ cRecv = [p \in participants |-> waiting]
    /\ cSent = [p \in participants |-> notsent]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ cAlive
    /\ ~cReq[p]
    /\ cReq' = [cReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cDecision, cRecv, cSent, pVote, pAlive, pDecision, pSent>>

CoordRecvVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cReq[p]
    /\ cRecv[p] = waiting
    /\ pSent[p]
    /\ cRecv' = [cRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<cAlive, cDecision, cReq, cSent, pVote, pAlive, pDecision, pSent>>

CoordDetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cReq[p]
    /\ cRecv[p] = waiting
    /\ ~pAlive[p]
    /\ cDecision' = abort
    /\ UNCHANGED <<cAlive, cReq, cRecv, cSent, pVote, pAlive, pDecision, pSent, pAlive>>

CoordMakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A q \in participants : cRecv[q] # waiting
    /\ IF \A q \in participants : cRecv[q] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED <<cAlive, cReq, cRecv, cSent, pVote, pAlive, pDecision, pSent>>

CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision \in {commit, abort}
    /\ cSent[p] = notsent
    /\ cSent' = [cSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<cAlive, cDecision, cReq, cRecv, pVote, pAlive, pDecision, pSent>>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ UNCHANGED <<cDecision, cReq, cRecv, cSent, pVote, pAlive, pDecision, pSent>>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
PartSendVote(p) ==
    /\ pAlive[p]
    /\ cReq[p]
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, cAlive, cDecision, cReq, cRecv, cSent>>

PartAbortOnNo(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pSent, cAlive, cDecision, cReq, cRecv, cSent>>

PartAbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ ~cReq[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pSent, cAlive, cDecision, cReq, cRecv, cSent>>

PartAdoptDecision(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cSent[p]]
    /\ UNCHANGED <<pVote, pAlive, pSent, cAlive, cDecision, cReq, cRecv, cSent>>

PartDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<pVote, pDecision, pSent, cAlive, cDecision, cReq, cRecv, cSent>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : CoordSendReq(p)
    \/ \E p \in participants : CoordRecvVote(p)
    \/ \E p \in participants : CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants : CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants : PartSendVote(p)
    \/ \E p \in participants : PartAbortOnNo(p)
    \/ \E p \in participants : PartAbortOnTimeout(p)
    \/ \E p \in participants : PartAdoptDecision(p)
    \/ \E p \in participants : PartDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pVote, pAlive, pDecision, pSent,
                     cAlive, cDecision, cReq, cRecv, cSent>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures variables range over intended domains)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSent \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cDecision \in {undecided, commit, abort}
    /\ cReq \in [participants -> BOOLEAN]
    /\ cRecv \in [participants -> {waiting} \cup {yes, no}]
    /\ cSent \in [participants -> {notsent, commit, abort}]

\* ----------------------------------------------------------------------
\* Safety invariant derived from AC1..AC4
\* ----------------------------------------------------------------------
Agreement ==
    \A p, q \in participants :
        (pDecision[p] = commit) => (pDecision[q] = commit)

CommitValidity ==
    \A p \in participants :
        (pDecision[p] = commit) => (\A q \in participants : pVote[q] = yes)

AbortValidity ==
    \A p \in participants :
        (pDecision[p] = abort) =>
            ( \E q \in participants : pVote[q] = no )
            \/ ( \E q \in participants : ~pAlive[q] )
            \/ ~cAlive

Irrevocability ==
    \A p \in participants :
        (pDecision[p] = commit) => [] (pDecision[p] = commit)
        /\ (pDecision[p] = abort) => [] (pDecision[p] = abort)

Safety == Agreement /\ CommitValidity /\ AbortValidity /\ Irrevocability

=============================================================================
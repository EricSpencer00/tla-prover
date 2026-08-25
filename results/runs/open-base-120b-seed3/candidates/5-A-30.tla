---- MODULE ACP_SB ----
EXTENDS FiniteSets, TLC

CONSTANTS 
    participants, \* set of participant identifiers
    yes, no,           \* possible votes
    undecided, commit, abort, \* decisions
    waiting, notsent   \* communication status

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    Vote,               \* Vote[p] \in {yes,no}
    pAlive,             \* pAlive[p] \in BOOLEAN
    pFaulty,            \* pFaulty[p] \in BOOLEAN
    pSent,              \* pSent[p]  \in BOOLEAN   (has the participant sent its vote)
    pDecision,          \* pDecision[p] \in {undecided, commit, abort}
    
    cAlive,             \* coordinator liveness
    cFaulty,            \* coordinator fault flag
    cRequested,         \* cRequested[p] = TRUE iff coordinator has sent a vote request to p
    cReceived,          \* cReceived[p] \in {yes,no,waiting}
    cSentDecision,      \* cSentDecision[p] \in {commit,abort,notsent}
    cDecision           \* coordinator's own decision \in {undecided, commit, abort}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Vars == << Vote, pAlive, pFaulty, pSent,
           pDecision,
           cAlive, cFaulty, cRequested,
           cReceived, cSentDecision,
           cDecision >>

AllReceived == \A p \in participants : cReceived[p] # waiting

AllSentDecision == \A p \in participants : cSentDecision[p] # notsent

AllRequestsSent == \A p \in participants : cRequested[p]

AllVotesYes == \A p \in participants : cReceived[p] = yes

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Vote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSent = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cRequested = [p \in participants |-> FALSE]
    /\ cReceived = [p \in participants |-> waiting]
    /\ cSentDecision = [p \in participants |-> notsent]
    /\ cDecision = undecided

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
SendReq(p) ==
    /\ cAlive
    /\ ~cRequested[p]
    /\ cRequested' = [cRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED << Vote, pAlive, pFaulty, pSent,
                    pDecision,
                    cAlive, cFaulty,
                    cReceived, cSentDecision, cDecision >>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]
    /\ cReceived[p] = waiting
    /\ pAlive[p]
    /\ pSent[p]
    /\ cReceived' = [cReceived EXCEPT ![p] = Vote[p]]
    /\ UNCHANGED << Vote, pAlive, pFaulty, pSent,
                    pDecision,
                    cAlive, cFaulty, cRequested,
                    cSentDecision, cDecision >>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]
    /\ cReceived[p] = waiting
    /\ ~pAlive[p]
    /\ ~pSent[p]
    /\ cDecision' = abort
    /\ UNCHANGED << Vote, pAlive, pFaulty, pSent,
                    pDecision,
                    cAlive, cFaulty, cRequested,
                    cReceived, cSentDecision,
                    cSentDecision >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ AllReceived
    /\ IF AllVotesYes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << Vote, pAlive, pFaulty, pSent,
                    pDecision,
                    cAlive, cFaulty, cRequested,
                    cReceived, cSentDecision >>

Broadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cSentDecision[p] = notsent
    /\ cSentDecision' = [cSentDecision EXCEPT ![p] = cDecision]
    /\ UNCHANGED << Vote, pAlive, pFaulty, pSent,
                    pDecision,
                    cAlive, cFaulty, cRequested,
                    cReceived, cDecision >>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << Vote, pAlive, pFaulty, pSent,
                    pDecision,
                    cRequested, cReceived,
                    cSentDecision, cDecision >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ pAlive[p]
    /\ ~pSent[p]
    /\ cRequested[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << Vote, pFaulty,
                    pDecision,
                    cAlive, cFaulty, cRequested,
                    cReceived, cSentDecision,
                    cDecision >>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSent[p]
    /\ Vote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << Vote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cRequested,
                    cReceived, cSentDecision,
                    cDecision >>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ ~cRequested[p]   \* coordinator died before sending request
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << Vote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cRequested,
                    cReceived, cSentDecision,
                    cDecision >>

DecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cSentDecision[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cSentDecision[p]]
    /\ UNCHANGED << Vote, pAlive, pFaulty, pSent,
                    cAlive, cFaulty, cRequested,
                    cReceived, cSentDecision,
                    cDecision >>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << Vote, pSent,
                    pDecision,
                    cAlive, cFaulty, cRequested,
                    cReceived, cSentDecision,
                    cDecision >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendReq(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideFromBroadcast(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ Vote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cRequested \in [participants -> BOOLEAN]
    /\ cReceived \in [participants -> {yes, no, waiting}]
    /\ cSentDecision \in [participants -> {commit, abort, notsent}]
    /\ cDecision \in {undecided, commit, abort}

\* ----------------------------------------------------------------------
\* Safety properties (as invariants)
\* ----------------------------------------------------------------------
AC1 == \A p1, p2 \in participants :
            (pDecision[p1] = commit) => (pDecision[p2] # abort)

AC2 == \A p \in participants :
            (pDecision[p] = commit) => \A q \in participants : Vote[q] = yes

AC3 == \A p \in participants :
            (pDecision[p] = abort) =>
                (\E q \in participants : Vote[q] = no) \/
                (\E q \in participants : pFaulty[q]) \/
                cFaulty

AC4 == \A p \in participants :
            (pDecision[p] = commit) => 
                [] (pDecision[p] = commit)  \* once committed, always committed
        /\ (pDecision[p] = abort) =>
                [] (pDecision[p] = abort)   \* once aborted, always aborted

\* ----------------------------------------------------------------------
\* Liveness property (weak)
\* ----------------------------------------------------------------------
Liveness ==
    <> ( \A p \in participants : pDecision[p] # undecided )
    \/ <> ( \E p \in participants : pFaulty[p] )
    \/ <> cFaulty

\* ----------------------------------------------------------------------
\* Exported names
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInv

\* The main specification and the invariant required by the .cfg file
\* (the .cfg will refer to SPECIFICATION == Spec, INVARIANT == TypeInv)
====
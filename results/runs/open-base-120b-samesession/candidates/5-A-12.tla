---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be defined in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    pVote,          \* [participants -> {yes,no}]
    pAlive,         \* [participants -> BOOLEAN]
    pFaulty,        \* [participants -> BOOLEAN]
    pDecision,      \* [participants -> {undecided,commit,abort}]
    pSentVote,      \* [participants -> BOOLEAN]
    pRequested,     \* [participants -> BOOLEAN]   \* coordinator sent request?
    
    cAlive,         \* BOOLEAN
    cFaulty,        \* BOOLEAN
    cDecision,      \* {undecided,commit,abort}
    cRequested,     \* [participants -> BOOLEAN]   \* request sent?
    cVotes,         \* [participants -> {yes,no,waiting}]
    cBroadcast      \* [participants -> {commit,abort,notsent}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Vars == << pVote, pAlive, pFaulty, pDecision, pSentVote, pRequested,
           cAlive, cFaulty, cDecision, cRequested, cVotes, cBroadcast >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSentVote = [p \in participants |-> FALSE]
    /\ pRequested = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cDecision = undecided
    /\ cRequested = [p \in participants |-> FALSE]
    /\ cVotes = [p \in participants |-> waiting]
    /\ cBroadcast = [p \in participants |-> notsent]

\* ----------------------------------------------------------------------
\* Coordinator actions
\* ----------------------------------------------------------------------
CoordSendReq(p) ==
    /\ cAlive
    /\ ~cRequested[p]
    /\ cRequested' = [cRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    pSentVote, pRequested,
                    cAlive, cFaulty, cDecision, cVotes, cBroadcast >>

CoordReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]
    /\ cVotes[p] = waiting
    /\ pSentVote[p]
    /\ pAlive[p]
    /\ cVotes' = [cVotes EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    pSentVote, pRequested,
                    cAlive, cFaulty, cDecision, cRequested, cBroadcast >>

CoordDetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]
    /\ cVotes[p] = waiting
    /\ ~pAlive[p]
    /\ ~pSentVote[p]
    /\ cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    pSentVote, pRequested,
                    cAlive, cFaulty, cRequested, cVotes, cBroadcast >>

CoordMakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants: cVotes[p] # waiting
    /\ IF \A p \in participants: cVotes[p] = yes
          THEN cDecision' = commit
          ELSE cDecision' = abort
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    pSentVote, pRequested,
                    cAlive, cFaulty, cRequested, cVotes, cBroadcast >>

CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cBroadcast[p] = notsent
    /\ cBroadcast' = [cBroadcast EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    pSentVote, pRequested,
                    cAlive, cFaulty, cDecision, cRequested, cVotes >>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pVote, pAlive, pFaulty, pDecision,
                    pSentVote, pRequested,
                    cDecision, cRequested, cVotes, cBroadcast >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
ParticipantSendVote(p) ==
    /\ pAlive[p]
    /\ ~pSentVote[p]
    /\ pRequested[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pFaulty, pDecision,
                    pAlive, pRequested,
                    cAlive, cFaulty, cDecision, cRequested, cVotes, cBroadcast >>

ParticipantAbortOnVote(p) ==
    /\ pAlive[p]
    /\ pSentVote[p]
    /\ pVote[p] = no
    /\ pDecision[p] = undecided
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                    pRequested,
                    cAlive, cFaulty, cDecision, cRequested, cVotes, cBroadcast >>

ParticipantAbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ ~cRequested[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                    pRequested,
                    cAlive, cFaulty, cDecision, cRequested, cVotes, cBroadcast >>

ParticipantDecideFromBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cBroadcast[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cBroadcast[p]]
    /\ UNCHANGED << pVote, pAlive, pFaulty, pSentVote,
                    pRequested,
                    cAlive, cFaulty, cDecision, cRequested, cVotes, cBroadcast >>

ParticipantDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pVote, pDecision, pSentVote,
                    pRequested,
                    cAlive, cFaulty, cDecision, cRequested, cVotes, cBroadcast >>

\* ----------------------------------------------------------------------
\* Composite next-state relation
\* ----------------------------------------------------------------------
CoordProgress ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordMakeDecision
    \/ \E p \in participants: CoordBroadcast(p)

ParticipantProgress(p) ==
    \/ ParticipantSendVote(p)
    \/ ParticipantAbortOnVote(p)
    \/ ParticipantAbortOnTimeout(p)
    \/ ParticipantDecideFromBroadcast(p)

Next ==
    \/ CoordProgress
    \/ \E p \in participants: ParticipantProgress(p)
    \/ \E p \in participants: ParticipantDie(p)
    \/ CoordDie

\* ----------------------------------------------------------------------
\* Fairness (weak fairness on progress actions, not on death)
\* ----------------------------------------------------------------------
CoordinatorFairness == WF_Vars(CoordProgress)
ParticipantFairness ==
    \A p \in participants: WF_Vars(ParticipantProgress(p))

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_Vars /\ CoordinatorFairness /\ ParticipantFairness

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ pRequested \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cDecision \in {undecided, commit, abort}
    /\ cRequested \in [participants -> BOOLEAN]
    /\ cVotes \in [participants -> {yes, no, waiting}]
    /\ cBroadcast \in [participants -> {commit, abort, notsent}]

\* ----------------------------------------------------------------------
\* Safety properties (as invariants, can be checked separately)
\* ----------------------------------------------------------------------
\* Agreement: no two participants decide differently
Agreement ==
    \A p,q \in participants :
        (pDecision[p] = commit => pDecision[q] = commit) /\
        (pDecision[p] = abort  => pDecision[q] = abort)

\* Commit validity
CommitValidity ==
    \A p \in participants :
        (pDecision[p] = commit) => \A q \in participants : pVote[q] = yes

\* Abort validity
AbortValidity ==
    \A p \in participants :
        (pDecision[p] = abort) =>
            ( \E q \in participants : pVote[q] = no ) \/
            ( \E q \in participants : pFaulty[q] ) \/
            cFaulty

\* Irrevocability
Irrevocability ==
    \A p \in participants :
        /\ (pDecision[p] = commit) => [] (pDecision[p] = commit)
        /\ (pDecision[p] = abort ) => [] (pDecision[p] = abort)

\* Liveness component AC3 (blocking condition)
Liveness_AC3 ==
    <> ( \A p \in participants : pDecision[p] # undecided )
        \/ ( \E p \in participants : pFaulty[p] )
        \/ cFaulty

====
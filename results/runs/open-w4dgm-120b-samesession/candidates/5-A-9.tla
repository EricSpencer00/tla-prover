---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Types: vote (yes/no), decision (commit/abort/undecided), basic on/off flags.
VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

TypeInv =
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ cRequested \in [participants -> BOOLEAN]
    /\ cRecv \in [participants -> {waiting, yes, no}]
    /\ cSent \in [participants -> {notsent, commit, abort}]
    /\ cDecision \in {undecided, commit, abort}
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN

Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSent = [p \in participants |-> FALSE]
    /\ cRequested = [p \in participants |-> FALSE]
    /\ cRecv = [p \in participants |-> waiting]
    /\ cSent = [p \in participants |-> notsent]
    /\ cDecision = undecided
    /\ cAlive = TRUE
    /\ cFaulty = FALSE

\* Coordinator emits one request message per participant; broadcast is one-at-a-time.
Request(p) ==
    /\ cAlive
    /\ ~cRequested[p]
    /\ cRequested' = [cRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRecv, cSent, cDecision, cAlive, cFaulty>>

RecvVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A q \in participants : cRequested[q]
    /\ cRecv[p] = waiting
    /\ pSent[p]
    /\ cRecv' = [cRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cSent, cDecision, cAlive, cFaulty>>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A q \in participants : cRequested[q]
    /\ cRecv[p] = waiting
    /\ pFaulty[p]
    /\ cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cSent, cAlive, cFaulty>>

Decide ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants : cRecv[p] # waiting
    /\ cDecision' = IF \A p \in participants : cRecv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cSent, cAlive, cFaulty>>

Broadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cSent[p] = notsent
    /\ cSent' = [cSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cDecision, cAlive, cFaulty>>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cSent, cDecision>>

\* A participant that has voted no aborts on its own.
AbortOnNo(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

AbortOnNoRequest(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cRequested[p]
    /\ cFaulty
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

DecideFromCoord(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cSent[p]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

SendVote(p) ==
    /\ pAlive[p]
    /\ ~pSent[p]
    /\ cRequested[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

PartDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecision, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

CoordProgress == Decide \/ \E p \in participants : Broadcast(p)
PartProgress == \E p \in participants : SendVote(p) \/ AbortOnNo(p) \/ DecidedFromCoord(p)

Next ==
    \/ CoordProgress \/ PartProgress
    \/ \E p \in participants : Request(p) \/ RecvVote(p) \/ DetectFault(p) \/ AbortOnNo(p) \/ AbortOnNoRequest(p) \/ DecideFromCoord(p) \/ SendVote(p) \/ PartDie(p)
    \/ CoordDie

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordProgress) /\ WF_vars(PartProgress)

\* SAFETY: an undecided participant can only become decided by matching the coordinator.
DecisionAgreement ==
    \A p \in participants :
        pDecision[p] # undecided => (cDecision # undecided /\ pDecision[p] = cDecision)

ValidCommit == \A p \in participants : pDecision[p] = commit => (\A q \in participants : pVote[q] = yes)

ValidAbort ==
    \A p \in participants :
        pDecision[p] = abort =>
            \/ (\E q \in participants : pVote[q] = no)
            \/ (\E q \in participants : pFaulty[q])
            \/ cFaulty

Irrevocable ==
    \A p \in participants :
        /\ (pDecision[p] = commit  => [pDecision EXCEPT ![p] = commit]  = pDecision)
        /\ (pDecision[p] = abort   => [pDecision EXCEPT ![p] = abort]   = pDecision)

\* LIVENESS: the transaction eventually resolves or fails visibly.
EventualResolution ==
    <>(\A p \in participants : pDecision[p] # undecided \/ pFaulty[p]) \/ cFaulty

====
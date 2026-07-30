---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent,
           cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ cRequested \in [participants -> BOOLEAN]
    /\ cRecv \in [participants -> {yes, no, waiting}]
    /\ cSent \in [participants -> {commit, abort, notsent}]
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

SendRequest(p) ==
    /\ cAlive
    /\ ~cRequested[p]
    /\ cRequested' = [cRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRecv, cSent, cDecision, cAlive, cFaulty>>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]
    /\ cRecv[p] = waiting
    /\ pSent[p]
    /\ cRecv' = [cRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cSent, cDecision, cAlive, cFaulty>>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]
    /\ cRecv[p] = waiting
    /\ ~pAlive[p]
    /\ cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cRecv, cSent, cAlive, cFaulty>>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants : cRecv[p] # waiting
    /\ cDecision' = IF \A p \in participants : cRecv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cRecv, cSent, cAlive, cFaulty>>

BroadcastDecision(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cSent[p] = notsent
    /\ cSent' = [cSent EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cRecv, cDecision, cAlive, cFaulty>>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

SendVote(p) ==
    /\ pAlive[p]
    /\ cRequested[p]
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty,
                  cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                  cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ ~cAlive
    /\ ~cRequested[p]
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                  cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

DecideFromCoordinator(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ cSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = cSent[p]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                  cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

PartDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecision, pSent,
                  cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

Next ==
    \/ \E p \in participants : SendRequest(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideFromCoordinator(p)
    \/ \E p \in participants : PartDie(p)

PartProgress == \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideFromCoordinator(p)
CoordProgress == MakeDecision \/ \E p \in participants : BroadcastDecision(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(PartProgress)
    /\ WF_vars(CoordProgress)

AC1 == \A p \in participants : pDecision[p] = commit => (\A q \in participants : pDecision[q] = commit)
AC2 == \A p \in participants : pDecision[p] = commit => \A q \in participants : pVote[q] = yes
AC3 == \A p \in participants : pDecision[p] = abort => (\E q \in participants : pVote[q] = no \/ pFaulty[q] \/ cFaulty)
AC4 ==
    \A p \in participants :
        /\ (pDecision[p] = commit) ~> (pDecision[p] = commit)
        /\ (pDecision[p] = abort) ~> (pDecision[p] = abort)

AC3L ==
    <>(\A p \in participants : pDecision[p] # undecided) \/ (\E p \in participants : pFaulty[p]) \/ cFaulty

====
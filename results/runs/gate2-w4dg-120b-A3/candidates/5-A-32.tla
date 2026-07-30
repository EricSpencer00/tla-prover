---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
    pVote, pAlive, pDecision, pFaulty, pSent,
    cRequested, cRecv, cSent, cDecision, cAlive, cFaulty

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
    /\ cDecision \in {commit, abort, undecided}
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN

Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [pa \in participants |-> TRUE]
    /\ pDecision = [pa \in participants |-> undecided]
    /\ pFaulty = [pa \in participants |-> FALSE]
    /\ pSent = [pa \in participants |-> FALSE]
    /\ cRequested = [pa \in participants |-> FALSE]
    /\ cRecv = [pa \in participants |-> waiting]
    /\ cSent = [pa \in participants |-> notsent]
    /\ cDecision = undecided
    /\ cAlive = TRUE
    /\ cFaulty = FALSE

SendRequest(pa) ==
    /\ cAlive
    /\ ~cRequested[pa]
    /\ cRequested' = [cRequested EXCEPT ![pa] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRecv, cSent, cDecision, cAlive, cFaulty>>

ReceiveVote(pa) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A pb \in participants : cRequested[pb]
    /\ cRecv[pa] = waiting
    /\ pSent[pa]
    /\ cRecv' = [cRecv EXCEPT ![pa] = pVote[pa]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cSent, cDecision, cAlive, cFaulty>>

DetectParticipantFault(pa) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A pb \in participants : cRequested[pb]
    /\ cRecv[pa] = waiting
    /\ ~pAlive[pa]
    /\ pSent[pa] = FALSE
    /\ cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cRecv, cSent, cAlive, cFaulty>>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A pa \in participants : cRecv[pa] # waiting
    /\ cDecision' = IF \A pa \in participants : cRecv[pa] = yes
                    THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cRecv, cSent, cAlive, cFaulty>>

BroadcastDecision(pa) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cSent[pa] = notsent
    /\ cSent' = [cSent EXCEPT ![pa] = cDecision]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cRecv, cDecision, cAlive, cFaulty>>

SendVote(pa) ==
    /\ pAlive[pa]
    /\ cRequested[pa]
    /\ pSent[pa] = FALSE
    /\ pSent' = [pSent EXCEPT ![pa] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty,
                  cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

AbortOnVote(pa) ==
    /\ pAlive[pa]
    /\ pDecision[pa] = undecided
    /\ pSent[pa]
    /\ pVote[pa] = no
    /\ pDecision' = [pDecision EXCEPT ![pa] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested,
                  cRecv, cSent, cDecision, cAlive, cFaulty>>

AbortOnTimeout(pa) ==
    /\ pAlive[pa]
    /\ pDecision[pa] = undecided
    /\ ~cAlive
    /\ ~cRequested[pa]
    /\ pDecision' = [pDecision EXCEPT ![pa] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested,
                  cRecv, cSent, cDecision, cAlive, cFaulty>>

DecideOnBroadcast(pa) ==
    /\ pAlive[pa]
    /\ pDecision[pa] = undecided
    /\ cSent[pa] # notsent
    /\ pDecision' = [pDecision EXCEPT ![pa] = cSent[pa]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested,
                  cRecv, cSent, cDecision, cAlive, cFaulty>>

DieCoordinator ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cRecv, cSent, cDecision>>

DieParticipant(pa) ==
    /\ pAlive[pa]
    /\ pAlive' = [pAlive EXCEPT ![pa] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![pa] = TRUE]
    /\ UNCHANGED <<pVote, pDecision, pSent, cRequested,
                  cRecv, cSent, cDecision, cAlive, cFaulty>>

DecideCoordinator(pa) ==
    /\ cSent[pa] # notsent
    /\ pDecision[pa] = undecided
    /\ pDecision' = [pDecision EXCEPT ![pa] = cSent[pa]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested,
                  cRecv, cSent, cDecision, cAlive, cFaulty>>

ParticipantProgress(pa) ==
    \/ SendVote(pa) \/ AbortOnVote(pa) \/ AbortOnTimeout(pa)
    \/ DecideOnBroadcast(pa) \/ DieParticipant(pa) \/ DecideCoordinator(pa)

CoordinatorProgress ==
    \/ \E pa \in participants : SendRequest(pa)
    \/ \E pa \in participants : ReceiveVote(pa)
    \/ \E pa \in participants : DetectParticipantFault(pa)
    \/ MakeDecision
    \/ \E pa \in participants : BroadcastDecision(pa)
    \/ DieCoordinator

Next ==
    \/ CoordinatorProgress
    \/ \E pa \in participants : ParticipantProgress(pa)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CoordinatorProgress)
    /\ \A pa \in participants : SF_vars(ParticipantProgress(pa))

AC1 ==
    \A pa, pb \in participants :
        ~(pDecision[pa] = commit /\ pDecision[pb] = abort)

AC2 ==
    \A pa \in participants : pDecision[pa] = commit => \A pb \in participants : pVote[pb] = yes

AC3 ==
    \A pa \in participants : pDecision[pa] = abort =>
        \/ \E pb \in participants : pVote[pb] = no
        \/ \E pb \in participants : pFaulty[pb]
        \/ cFaulty

AC4 ==
    \A pa \in participants :
        (pDecision[pa] = commit) ~> (pDecision[pa] = commit)
        /\ (pDecision[pa] = abort) ~> (pDecision[pa] = abort)

EventualDecision ==
    \A pa \in participants : (pDecision[pa] = undecided) ~> (pDecision[pa] # undecided)

DecideOrFault ==
    <>(\A pa \in participants : pDecision[pa] # undecided \/ pFaulty[pa] \/ cFaulty)

====
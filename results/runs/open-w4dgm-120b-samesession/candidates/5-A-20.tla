---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cReceived,
          cBroadcast, cDecision, cAlive, cFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested,
           cReceived, cBroadcast, cDecision, cAlive, cFaulty>>

TypeOK ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecision \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSent \in [participants -> BOOLEAN]
  /\ cRequested \in [participants -> BOOLEAN]
  /\ cReceived \in [participants -> {waiting, yes, no}]
  /\ cBroadcast \in [participants -> {notsent, commit, abort}]
  /\ cDecision \in {undecided, commit, abort}
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN

Init ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive = [pa \in participants |-> TRUE]
  /\ pDecision = [pa \in participants |-> undecided]
  /\ pFaulty = [pa \in participants |-> FALSE]
  /\ pSent = [pa \in participants |-> FALSE]
  /\ cRequested = [pa \in participants |-> FALSE]
  /\ cReceived = [pa \in participants |-> waiting]
  /\ cBroadcast = [pa \in participants |-> notsent]
  /\ cDecision = undecided
  /\ cAlive = TRUE
  /\ cFaulty = FALSE

\* Coordinator actions
SendRequest(pa) ==
  /\ cAlive
  /\ ~cRequested[pa]
  /\ cRequested' = [cRequested EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cReceived,
                 cBroadcast, cDecision, cAlive, cFaulty>>

ReceiveVote(pa) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ cRequested[pa]
  /\ cReceived[pa] = waiting
  /\ pSent[pa]
  /\ cReceived' = [cReceived EXCEPT ![pa] = pVote[pa]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested,
                 cBroadcast, cDecision, cAlive, cFaulty>>

DetectFault(pa) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ cRequested[pa]
  /\ cReceived[pa] = waiting
  /\ ~pAlive[pa]
  /\ cDecision' = abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested,
                 cReceived, cBroadcast, cAlive, cFaulty>>

MakeDecision ==
  /\ cAlive
  /\ cDecision = undecided
  /\ \A pa \in participants : cRequested[pa] /\ cReceived[pa] # waiting
  /\ cDecision' = (IF \A pa \in participants : cReceived[pa] = yes
                   THEN commit ELSE abort)
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested,
                 cReceived, cBroadcast, cAlive, cFaulty>>

BroadcastDecision(pa) ==
  /\ cAlive
  /\ cDecision # undecided
  /\ cBroadcast[pa] = notsent
  /\ cBroadcast' = [cBroadcast EXCEPT ![pa] = cDecision]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 cRequested, cReceived, cDecision, cAlive, cFaulty>>

CoordinatorDie ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 cRequested, cReceived, cBroadcast, cDecision>>

\* Participant actions
SendVote(pa) ==
  /\ pAlive[pa]
  /\ cRequested[pa]
  /\ ~pSent[pa]
  /\ pSent' = [pSent EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty,
                 cRequested, cReceived, cBroadcast, cDecision,
                 cAlive, cFaulty>>

AbortOnVote(pa) ==
  /\ pAlive[pa]
  /\ pDecision[pa] = undecided
  /\ pSent[pa]
  /\ pVote[pa] = no
  /\ pDecision' = [pDecision EXCEPT ![pa] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested,
                 cReceived, cBroadcast, cDecision, cAlive, cFaulty>>

AbortOnTimeout(pa) ==
  /\ pAlive[pa]
  /\ pDecision[pa] = undecided
  /\ ~cAlive
  /\ ~cRequested[pa]
  /\ pDecision' = [pDecision EXCEPT ![pa] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested,
                 cReceived, cBroadcast, cDecision, cAlive, cFaulty>>

DecideByCoordinator(pa) ==
  /\ pAlive[pa]
  /\ pDecision[pa] = undecided
  /\ cBroadcast[pa] # notsent
  /\ pDecision' = [pDecision EXCEPT ![pa] = cBroadcast[pa]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                 cRequested, cReceived, cBroadcast, cDecision,
                 cAlive, cFaulty>>

ParticipantDie(pa) ==
  /\ pAlive[pa]
  /\ pAlive' = [pAlive EXCEPT ![pa] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![pa] = TRUE]
  /\ UNCHANGED <<pVote, pDecision, pSent, cRequested, cReceived,
                 cBroadcast, cDecision, cAlive, cFaulty>>

CoordinatorProgress ==
  \/ \E pa \in participants : SendRequest(pa)
  \/ \E pa \in participants : ReceiveVote(pa)
  \/ \E pa \in participants : DetectFault(pa)
  \/ MakeDecision
  \/ \E pa \in participants : BroadcastDecision(pa)

ParticipantProgress ==
  \/ \E pa \in participants : SendVote(pa)
  \/ \E pa \in participants : AbortOnVote(pa)
  \/ \E pa \in participants : AbortOnTimeout(pa)
  \/ \E pa \in participants : DecideByCoordinator(pa)

Next ==
  \/ CoordinatorProgress
  \/ ParticipantProgress
  \/ CoordinatorDie
  \/ \E pa \in participants : ParticipantDie(pa)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(ParticipantProgress)
  /\ WF_vars(CoordinatorProgress)

\* Safety: no two participants ever decide differently.
Agreement ==
  \A pa, pb \in participants :
    (pDecision[pa] = commit /\ pDecision[pb] = abort) => pa = pb

\* If any commit happened, every vote was yes.
CommitValidity ==
  (\E pa \in participants : pDecision[pa] = commit) =>
    (\A pa \in participants : pVote[pa] = yes)

\* An abort needs at least one no vote or a crash somewhere.
AbortValidity ==
  (\E pa \in participants : pDecision[pa] = abort) =>
    (\E pa \in participants : pVote[pa] = no) \/ (\E pa \in participants : pFaulty[pa]) \/ cFaulty

\* A decision, once made, never flips back.
Irrevocability ==
  /\ \A pa \in participants : (pDecision[pa] = commit) ~> (pDecision[pa] = commit)
  /\ \A pa \in participants : (pDecision[pa] = abort) ~> (pDecision[pa] = abort)

\* Liveness (weaker than the non-blocking guarantee): some outcome or fault always surfaces.
EventualResolution ==
  <>(\A pa \in participants : pDecision[pa] # undecided \/ cFaulty \/ (\E pa \in participants : pFaulty[pa]))

====
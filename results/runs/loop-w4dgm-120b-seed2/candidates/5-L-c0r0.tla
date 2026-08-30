---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* The simple broadcast variant can block if the coordinator crashes mid-broadcast,
\* so the non-blocking termination property AC5 is NOT satisfied here.
\* Safety properties AC1-AC4 are all satisfied.

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

TypeOK ==
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

\* Coordinator actions ---------------------------------------------------------

RequestVote(p) ==
  /\ cAlive
  /\ ~cRequested[p]
  /\ cRequested' = [cRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRecv, cSent, cDecision, cAlive, cFaulty>>

ReceiveVote(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ cRequested[p]
  /\ cRecv[p] = waiting
  /\ pSent[p]
  /\ cRecv' = [cRecv EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cSent, cDecision, cAlive, cFaulty>>

DetectFault(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ cRequested[p]
  /\ cRecv[p] = waiting
  /\ ~pAlive[p]
  /\ ~pSent[p]
  /\ cDecision' = abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cSent, cAlive, cFaulty>>

MakeDecision ==
  /\ cAlive
  /\ cDecision = undecided
  /\ \A p \in participants : cRequested[p]
  /\ \A p \in participants : cRecv[p] # waiting
  /\ cDecision' = IF \A p \in participants : cRecv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cSent, cAlive, cFaulty>>

BroadcastDecision(p) ==
  /\ cAlive
  /\ cDecision # undecided
  /\ cSent[p] = notsent
  /\ cSent' = [cSent EXCEPT ![p] = cDecision]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cDecision, cAlive, cFaulty>>

CoordinatorDie ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cRecv, cSent, cDecision>>

\* Participant actions ---------------------------------------------------------

SendVote(p) ==
  /\ pAlive[p]
  /\ cRequested[p]
  /\ ~pSent[p]
  /\ pSent' = [pSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

AbortOnVote(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ pSent[p]
  /\ pVote[p] = no
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

AbortOnTimeout(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ ~cAlive
  /\ ~cRequested[p]
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

DecideFromCoordinator(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ cSent[p] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = cSent[p]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

ParticipantDie(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pDecision, pSent, cRequested, cRecv, cSent, cDecision, cAlive, cFaulty>>

Next ==
  \/ \E p \in participants : RequestVote(p)
  \/ \E p \in participants : ReceiveVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : BroadcastDecision(p)
  \/ CoordinatorDie
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideFromCoordinator(p)
  \/ \E p \in participants : ParticipantDie(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants : WF_vars(SendVote(p))
  /\ \A p \in participants : WF_vars(DecideFromCoordinator(p))
  /\ \A p \in participants : WF_vars(AbortOnVote(p))
  /\ \A p \in participants : WF_vars(AbortOnTimeout(p))

\* Safety: no two participants ever decide differently.
Agreement ==
  \A p, q \in participants :
    (pDecision[p] = commit /\ pDecision[q] = abort) => FALSE

CommitValidity ==
  \A p \in participants : pDecision[p] = commit => (\A q \in participants : pVote[q] = yes)

AbortValidity ==
  \A p \in participants :
    pDecision[p] = abort =>
      \/ (\E q \in participants : pVote[q] = no)
      \/ (\E q \in participants : pFaulty[q])
      \/ cFaulty

Irrevocability ==
  \A p \in participants :
    /\ (pDecision[p] = commit => (pDecision' [p] = commit))
    /\ (pDecision[p] = abort => (pDecision' [p] = abort))

\* Liveness: either everyone decides, or some failure is exposed.
EventualDecisionOrFailure ==
  <>(\A p \in participants : pDecision[p] # undecided \/ cFaulty \/ (\E q \in participants : pFaulty[q]))

\* The simple broadcast variant does NOT guarantee non-blocking termination,
\* so AC5 (every non-faulty participant eventually decides) is omitted.
TypeInv == TypeOK

====
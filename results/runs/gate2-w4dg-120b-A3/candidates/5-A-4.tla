---- MODULE ACP_SB ----
EXTENDS Integers, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cReceived,
          cBroadcast, cDecision, cAlive, cFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent, cRequested, cReceived,
          cBroadcast, cDecision, cAlive, cFaulty>>

TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ cRequested \in [participants -> BOOLEAN]
    /\ cReceived \in [participants -> {yes, no, waiting}]
    /\ cBroadcast \in [participants -> {commit, abort, notsent}]
    /\ cDecision \in {decided, undecided}
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN

Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSent = [p \in participants |-> FALSE]
    /\ cRequested = [p \in participants |-> FALSE]
    /\ cReceived = [p \in participants |-> waiting]
    /\ cBroadcast = [p \in participants |-> notsent]
    /\ cDecision = undecided
    /\ cAlive = TRUE
    /\ cFaulty = FALSE

RequestVote ==
    /\ cAlive
    /\ \E p \in participants :
         /\ ~cRequested[p]
         /\ cRequested' = [cRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cReceived, cBroadcast, cDecision, cAlive, cFaulty>>

ReceiveVote ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \E p \in participants :
         /\ cRequested[p]
         /\ cReceived[p] = waiting
         /\ pSent[p]
         /\ cReceived' = [cReceived EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cBroadcast, cDecision, cAlive, cFaulty>>

DetectFault ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \E p \in participants :
         /\ cRequested[p]
         /\ cReceived[p] = waiting
         /\ ~pAlive[p]
         /\ cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cReceived, cBroadcast, cAlive, cFaulty>>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants : cReceived[p] # waiting
    /\ cDecision' = IF \A p \in participants : cReceived[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cReceived, cBroadcast, cAlive, cFaulty>>

BroadcastDecision ==
    /\ cAlive
    /\ cDecision # undecided
    /\ \E p \in participants :
         /\ cBroadcast[p] = notsent
         /\ cBroadcast' = [cBroadcast EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cReceived, cDecision, cAlive, cFaulty>>

CoordinatorDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  cRequested, cReceived, cBroadcast, cDecision, cFaulty>>

SendVote ==
    /\ \E p \in participants :
         /\ pAlive[p]
         /\ cRequested[p]
         /\ ~pSent[p]
         /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty,
                  cRequested, cReceived, cBroadcast, cDecision, cAlive, cFaulty>>

AbortOnVote ==
    /\ \E p \in participants :
         /\ pAlive[p]
         /\ pDecision[p] = undecided
         /\ pSent[p]
         /\ pVote[p] = no
         /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested,
                  cReceived, cBroadcast, cDecision, cAlive, cFaulty>>

AbortOnTimeout ==
    /\ \E p \in participants :
         /\ pAlive[p]
         /\ pDecision[p] = undecided
         /\ ~cRequested[p]
         /\ ~cAlive
         /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested,
                  cReceived, cBroadcast, cDecision, cAlive, cFaulty>>

DecideOnBroadcast ==
    /\ \E p \in participants :
         /\ pAlive[p]
         /\ pDecision[p] = undecided
         /\ cBroadcast[p] # notsent
         /\ pDecision' = [pDecision EXCEPT ![p] = cBroadcast[p]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, cRequested,
                  cReceived, cBroadcast, cDecision, cAlive, cFaulty>>

ParticipantDie ==
    /\ \E p \in participants :
         /\ pAlive[p]
         /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
         /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecision, pSent, cRequested,
                  cReceived, cBroadcast, cDecision, cAlive, cFaulty>>

Next ==
    \/ RequestVote \/ ReceiveVote \/ DetectFault \/ MakeDecision
    \/ BroadcastDecision \/ CoordinatorDie \/ SendVote \/ AbortOnVote
    \/ AbortOnTimeout \/ DecideOnBroadcast \/ ParticipantDie

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(SendVote)
    /\ WF_vars(AbortOnVote)
    /\ WF_vars(DecideOnBroadcast)
    /\ WF_vars(RequestVote)
    /\ WF_vars(ReceiveVote)
    /\ WF_vars(DetectFault)
    /\ WF_vars(MakeDecision)
    /\ WF_vars(BroadcastDecision)

AC1 == \A p, q \in participants : ~(pDecision[p] = commit /\ pDecision[q] = abort)

AC2 == \A p \in participants : pDecision[p] = commit => (\A q \in participants : pVote[q] = yes)

AC3 == \A p \in participants : pDecision[p] = abort =>
          \/ \E q \in participants : pVote[q] = no
          \/ \E q \in participants : pFaulty[q]
          \/ cFaulty

AC4 == \A p \in participants :
          /\ (pDecision[p] = commit => [pDecision EXCEPT ![p] = commit])
          /\ (pDecision[p] = abort => [pDecision EXCEPT ![p] = abort])

DecideLiveness ==
    (cAlive \/ cFaulty \/ (\A p \in participants : pDecision[p] # undecided)) ~>
      (cAlive \/ cFaulty \/ (\A p \in participants : pDecision[p] # undecided))

====
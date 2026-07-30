---- MODULE ACP_SB ----
\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB).  One coordinator
\* collects votes from participants and then broadcasts a commit/abort decision.
\* Simple broadcast means the coordinator can die mid-broadcast and leave a
\* participant undecided forever, so the protocol is not non-blocking under
\* failures (and that is intentional: the model captures the liveness bug).
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator decisions for each participant it has broadcast to (or notsent).
CoordVars == participants \cup {notsent}
Coords == [participants -> {commit, abort, notsent}]

VARIABLES pVote, pAlive, pDecision, pFaulty, pSentVote, sentTo, cVote,
         cDecision, cAlive, cFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSentVote, sentTo, cVote,
          cDecision, cAlive, cFaulty>>

TypeInv ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pDecision \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pSentVote \in [participants -> BOOLEAN]
  /\ sentTo \in [participants -> Coords]
  /\ cVote \in [participants -> {yes, no, waiting}]
  /\ cDecision \in {undecided, commit, abort}
  /\ cAlive \in BOOLEAN
  /\ cFaulty \in BOOLEAN

Init ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pDecision = [p \in participants |-> undecided]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ pSentVote = [p \in participants |-> FALSE]
  /\ sentTo = [p \in participants |-> notsent]
  /\ cVote = [p \in participants |-> waiting]
  /\ cDecision = undecided
  /\ cAlive = TRUE
  /\ cFaulty = FALSE

\* Coordinator actions.
SendVoteRequest(p) ==
  /\ cAlive
  /\ sentTo[p] = notsent
  /\ sentTo' = [sentTo EXCEPT ![p] = notsent]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                cVote, cDecision, cAlive, cFaulty>>

\* The coordinator receives a vote only after the participant has sent it.
ReceiveVote(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ \A q \in participants : sentTo[q] # notsent
  /\ cVote[p] = waiting
  /\ pSentVote[p]
  /\ cVote' = [cVote EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                sentTo, cDecision, cAlive, cFaulty>>

\* Failure detection is magical: the coordinator instantly knows a participant
\* is dead before it voted and aborts the whole transaction on that basis.
DetectParticipantFault(p) ==
  /\ cAlive
  /\ cDecision = undecided
  /\ \A q \in participants : sentTo[q] # notsent
  /\ cVote[p] = waiting
  /\ ~pAlive[p]
  /\ cDecision' = abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                sentTo, cVote, cAlive, cFaulty>>

MakeDecision ==
  /\ cAlive
  /\ cDecision = undecided
  /\ \A p \in participants : cVote[p] # waiting
  /\ cDecision' = IF \A p \in participants : cVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                sentTo, cVote, cAlive, cFaulty>>

BroadcastDecision(p) ==
  /\ cAlive
  /\ cDecision # undecided
  /\ sentTo[p] = notsent
  /\ sentTo' = [sentTo EXCEPT ![p] = cDecision]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                cVote, cDecision, cAlive, cFaulty>>

DieCoordinator ==
  /\ cAlive
  /\ cAlive' = FALSE
  /\ cFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                sentTo, cVote, cDecision>>

\* Participant actions.
SendVote(p) ==
  /\ pAlive[p]
  /\ sentTo[p] # notsent
  /\ ~pSentVote[p]
  /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, sentTo,
                cVote, cDecision, cAlive, cFaulty>>

AbortOnVote(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ pSentVote[p]
  /\ pVote[p] = no
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote, sentTo,
                cVote, cDecision, cAlive, cFaulty>>

AbortOnNoVoteRequest(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ ~cAlive
  /\ sentTo[p] = notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote, sentTo,
                cVote, cDecision, cAlive, cFaulty>>

DecideOnBroadcast(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = undecided
  /\ sentTo[p] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = sentTo[p]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote, sentTo,
                cVote, cDecision, cAlive, cFaulty>>

DieParticipant(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pDecision, pSentVote, sentTo,
                cVote, cDecision, cAlive, cFaulty>>

\* Actions that participants may take (excluding death, which is not fair).
ParticipantProgress ==
  \E p \in participants :
    \/ SendVote(p)
    \/ AbortOnVote(p)
    \/ AbortOnNoVoteRequest(p)
    \/ DecideOnBroadcast(p)

CoordinatorProgress ==
  \/ MakeDecision
  \/ \E p \in participants : BroadcastDecision(p)

Next ==
  \/ \E p \in participants : SendVoteRequest(p)
  \/ \E p \in participants : ReceiveVote(p)
  \/ \E p \in participants : DetectParticipantFault(p)
  \/ CoordinatorProgress
  \/ DieCoordinator
  \/ \E p \in participants : DieParticipant(p)
  \/ ParticipantProgress

\* Weak fairness: participants and the coordinator eventually make progress
\* when they are able (death takes no fairness).
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ParticipantProgress)
  /\ WF_vars(CoordinatorProgress)

\* Safety: no two participants ever decide differently, and a decision is
\* backed by a unanimous vote or a crash.
Agreement ==
  \A p \in participants : pDecision[p] = commit => \A q \in participants : pDecision[q] = commit

CommitValidity ==
  \E p \in participants : pDecision[p] = commit => \A q \in participants : pVote[q] = yes

AbortValidity ==
  \E p \in participants : pDecision[p] = abort =>
    \/ \E q \in participants : pVote[q] = no
    \/ \E q \in participants : pFaulty[q]
    \/ cFaulty

IrreversibleCommit ==
  \A p \in participants : (pDecision[p] = commit) ~> (pDecision[p] = commit)

IrreversibleAbort ==
  \A p \in participants : (pDecision[p] = abort) ~> (pDecision[p] = abort)

\* Liveness: the transaction eventually resolves one way or the other, or a
\* participant/crashes, which is the last progress the system can make.
Resolution == \A p \in participants : pDecision[p] # undecided

EventuallyResolved == Eventuall?(\A p \in participants : pDecision[p] # undecided)
EventuallyResolved ==
  \A p \in participants : (pDecision[p] # undecided) ~> (pDecision[p] # undecided)

Fixup ==
  Eventualy?(\A p \in participants : pDecision[p] # undecided \/ cFaulty \/ \E q \in participants : pFaulty[q])

EventuallyResolved == (\A p \in participants : pDecision[p] # undecided) \/ cFaulty \/ \E q \in participants : pFaulty[q]

====
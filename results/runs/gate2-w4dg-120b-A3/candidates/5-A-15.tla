---- MODULE ACP_SB ----
EXTENDS Naturals, TLC

\* This is TLA+ for the Atomic Commitment Protocol with Simple Broadcast
\* (ACP-SB) from Babaoglu and Toueg, including the extra liveness check
\* that is not guaranteed for the simple-broadcast variant: eventual
\* decision or failure of some participant/coordinator.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent, coordRequested, coordReceived,
          coordSent, coordDecision, coordAlive, coordFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent, coordRequested,
          coordReceived, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive \in BOOLEAN
  /\ pDecision \in [participants -> {undecided, commit, abort}]
  /\ pFaulty \in BOOLEAN
  /\ pSent \in [participants -> BOOLEAN]
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordReceived \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

\* The coordinator is alive and non-faulty, and has not asked for or acted.
CoordReady ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ \A p \in participants : ~coordRequested[p]
  /\ \A p \in participants : coordReceived[p] = waiting
  /\ coordDecision = undecided
  /\ \A p \in participants : coordSent[p] = notsent

\* The participants are alive, non-faulty, undecided, and have said nothing.
PartsReady ==
  /\ pAlive
  /\ ~pFaulty
  /\ \A p \in participants : pDecision[p] = undecided
  /\ \A p \in participants : ~pSent[p]

Init ==
  /\ pVote \in [participants -> {yes, no}]
  /\ pAlive = TRUE
  /\ pDecision = [p \in participants |-> undecided]
  /\ pFaulty = FALSE
  /\ pSent = [p \in participants |-> FALSE]
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordReceived = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator actions: send requests, receive votes, detect faults, decide,
\* broadcast decision with simple (sequential) broadcast, and die.
CoordSendRequest(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 coordReceived, coordSent, coordDecision,
                 coordAlive, coordFaulty>>

CoordReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordReceived[p] = waiting
  /\ pSent[p]
  /\ coordReceived' = [coordReceived EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 coordRequested, coordSent, coordDecision,
                 coordAlive, coordFaulty>>

CoordDetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordReceived[p] = waiting
  /\ ~pAlive
  /\ coordDecision' = abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 coordRequested, coordReceived, coordSent,
                 coordAlive, coordFaulty>>

CoordDecide ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordReceived[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordReceived[p] = yes
                       THEN commit ELSE abort
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 coordRequested, coordReceived, coordSent,
                 coordAlive, coordFaulty>>

CoordBroadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 coordRequested, coordReceived, coordDecision,
                 coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                 coordRequested, coordReceived, coordSent,
                 coordDecision>>

\* Participant actions: send vote, abort on own no vote, abort on timeout,
\* decide on coordinator broadcast, and die.
PartSendVote(p) ==
  /\ pAlive
  /\ coordRequested[p]
  /\ ~pSent[p]
  /\ pSent' = [pSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty,
                 coordRequested, coordReceived, coordSent,
                 coordDecision, coordAlive, coordFaulty>>

PartAbortOnVote(p) ==
  /\ pAlive
  /\ pDecision[p] = undecided
  /\ pSent[p]
  /\ pVote[p] = no
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                 coordRequested, coordReceived, coordSent,
                 coordDecision, coordAlive, coordFaulty>>

PartAbortOnTimeout(p) ==
  /\ pAlive
  /\ pDecision[p] = undecided
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                 coordRequested, coordReceived, coordSent,
                 coordDecision, coordAlive, coordFaulty>>

PartDecide(p) ==
  /\ pAlive
  /\ pDecision[p] = undecided
  /\ coordSent[p] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                 coordRequested, coordReceived, coordSent,
                 coordDecision, coordAlive, coordFaulty>>

PartDie ==
  /\ pAlive
  /\ pAlive' = FALSE
  /\ pFaulty' = TRUE
  /\ UNCHANGED <<pVote, pDecision, pSent,
                 coordRequested, coordReceived, coordSent,
                 coordDecision, coordAlive, coordFaulty>>

PartStep == \E p \in participants :
  PartSendVote(p) \/ PartAbortOnVote(p) \/ PartAbortOnTimeout(p)
  \/ PartDecide(p) \/ PartDie

CoordinatorStep ==
  \/ CoordDecide
  \/ \E p \in participants : CoordSendRequest(p) \/ CoordReceiveVote(p)
     \/ CoordDetectFault(p) \/ CoordBroadcast(p) \/ CoordDie

Next ==
  \/ PartStep
  \/ CoordinatorStep

\* Weak fairness on progress actions (not on death): a participant or the
\* coordinator that can make progress eventually does.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(PartStep)
  /\ WF_vars(CoordinatorStep)

\* Safety: agreement, commit requires all yes votes, abort needs at least one
\* no vote or a crash, and decisions are irreversible.
Agreement ==
  ~ (\E p \in participants : pDecision[p] = commit /\ \E q \in participants : pDecision[q] = abort)

CommitValid ==
  (\E p \in participants : pDecision[p] = commit) => (\A q \in participants : pVote[q] = yes)

AbortValid ==
  (\E p \in participants : pDecision[p] = abort)
    => (\E q \in participants : pVote[q] = no \/ pFaulty \/ coordFaulty)

Irreversible ==
  /\ (\A p \in participants : pDecision[p] = commit) ~> (\A p \in participants : pDecision[p] = commit)
  /\ (\A p \in participants : pDecision[p] = abort) ~> (\A p \in participants : pDecision[p] = abort)

\* Liveness: eventual decision by all or a failure somewhere; not guaranteed
\* for ACP-SB, but it is the property the model is required to check.
EventualDecisionOrFailure ==
  <>(\A p \in participants : pDecision[p] # undecided \/ pFaulty \/ coordFaulty)

====
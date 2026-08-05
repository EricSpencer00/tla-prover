---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* An ACP-SB (Atomic Commitment with Simple Broadcast) protocol.  The coordinator
\* collects votes, decides commit or abort, and then broadcasts the decision to
\* each participant sequentially (the "simple broadcast" variant).  A crash of
\* the coordinator during broadcast can strand a participant undecided, so this
\* protocol is not non-blocking; it only guarantees that some decision is reached
\* or some node has crashed.

VARIABLES coordAlive, coordFaulty, coordDecision, coordVotedYes, coordDecided,
          coordRequested, coordRecv, partAlive, partFaulty, partDecision,
          partSentVote

vars == <<coordAlive, coordFaulty, coordDecision, coordVotedYes, coordDecided,
          coordRequested, coordRecv, partAlive, partFaulty, partDecision,
          partSentVote>>

TypeInv ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordVotedYes \in BOOLEAN
  /\ coordDecided \in BOOLEAN
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordRecv \in [participants -> {yes, no, waiting}]
  /\ partAlive \in [participants -> BOOLEAN]
  /\ partFaulty \in [participants -> BOOLEAN]
  /\ partDecision \in [participants -> {undecided, commit, abort}]
  /\ partSentVote \in [participants -> BOOLEAN]

Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = undecided
  /\ coordVotedYes = FALSE
  /\ coordDecided = FALSE
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordRecv = [p \in participants |-> waiting]
  /\ partAlive = [p \in participants |-> TRUE]
  /\ partFaulty = [p \in participants |-> FALSE]
  /\ partDecision = [p \in participants |-> undecided]
  /\ partSentVote = [p \in participants |-> FALSE]
  /\ \E f \in [participants -> {yes, no}]:
       /\ f \in [participants -> {yes, no}]
       /\ \A p \in participants: partSentVote[p] = FALSE

\* The coordinator sends a vote request to a participant.
SendRequest(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotedYes,
                coordDecided, coordRecv, partAlive, partFaulty,
                partDecision, partSentVote>>

\* The coordinator receives a participant's vote (only if that participant has
\* actually sent it).
ReceiveVote(p) ==
  /\ coordAlive
  /\ ~coordDecided
  /\ coordRequested[p]
  /\ coordRecv[p] = waiting
  /\ partSentVote[p]
  /\ coordRecv' = [coordRecv EXCEPT ![p] = partDecision[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotedYes,
                coordDecided, coordRequested, partAlive, partFaulty,
                partDecision, partSentVote>>

\* Failure detection: a participant that has died without voting forces an abort.
DetectFault(p) ==
  /\ coordAlive
  /\ ~coordDecided
  /\ coordRequested[p]
  /\ coordRecv[p] = waiting
  /\ partFaulty[p]
  /\ coordDecision' = abort
  /\ coordDecided' = TRUE
  /\ UNCHANGED <<coordAlive, coordFaulty, coordVotedYes, coordRequested,
                coordRecv, partAlive, partFaulty, partDecision, partSentVote>>

\* The coordinator decides commit only if every participant voted yes.
Decide ==
  /\ coordAlive
  /\ ~coordDecided
  /\ \A p \in participants: coordRecv[p] # waiting
  /\ coordDecision' = (IF \A p \in participants: coordRecv[p] = yes
                        THEN commit ELSE abort)
  /\ coordDecided' = TRUE
  /\ coordVotedYes' = \A p \in participants: coordRecv[p] = yes
  /\ UNCHANGED <<coordAlive, coordFaulty, coordRequested, coordRecv,
                partAlive, partFaulty, partDecision, partSentVote>>

\* Simple (sequential) broadcast: the coordinator sends its decision to one
\* participant at a time.
Broadcast(p) ==
  /\ coordAlive
  /\ coordDecided
  /\ partDecision[p] = undecided
  /\ partDecision' = [partDecision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotedYes,
                coordDecided, coordRequested, coordRecv, partAlive,
                partFaulty, partSentVote>>

\* The coordinator crashes.
CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, coordVotedYes, coordDecided, coordRequested,
                coordRecv, partAlive, partFaulty, partDecision, partSentVote>>

\* A participant sends its vote to the coordinator.
SendVote(p) ==
  /\ partAlive[p]
  /\ coordRequested[p]
  /\ ~partSentVote[p]
  /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotedYes,
                coordDecided, coordRequested, coordRecv, partAlive,
                partFaulty, partDecision>>

\* A participant aborts on its own vote being no.
AbortOnVote(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ partSentVote[p]
  /\ coordRecv[p] = no
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotedYes,
                coordDecided, coordRequested, coordRecv, partAlive,
                partFaulty, partSentVote>>

\* A participant times out waiting for a coordinator that has died: it aborts.
AbortOnTimeout(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotedYes,
                coordDecided, coordRequested, coordRecv, partAlive,
                partFaulty, partSentVote>>

\* A participant adopts the coordinator's broadcast decision.
DecideFromBroadcast(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ partDecision' = [partDecision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotedYes,
                coordDecided, coordRequested, coordRecv, partAlive,
                partFaulty, partSentVote>>

\* A participant crashes.
PartDie(p) ==
  /\ partAlive[p]
  /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
  /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordVotedYes,
                coordDecided, coordRequested, coordRecv, partDecision,
                partSentVote>>

Next ==
  \/ \E p \in participants: SendRequest(p)
  \/ \E p \in participants: ReceiveVote(p)
  \/ \E p \in participants: DetectFault(p)
  \/ Decide
  \/ \E p \in participants: Broadcast(p)
  \/ CoordDie
  \/ \E p \in participants: SendVote(p)
  \/ \E p \in participants: AbortOnVote(p)
  \/ \E p \in participants: AbortOnTimeout(p)
  \/ \E p \in participants: DecideFromBroadcast(p)
  \/ \E p \in participants: PartDie(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants: WF_vars(SendVote(p))
  /\ \A p \in participants: WF_vars(DecideFromBroadcast(p))
  /\ \A p \in participants: WF_vars(AbortOnVote(p))
  /\ \A p \in participants: WF_vars(AbortOnTimeout(p))
  /\ \A p \in participants: WF_vars(Broadcast(p))
  /\ \A p \in participants: WF_vars(SendRequest(p))
  /\ \A p \in participants: WF_vars(ReceiveVote(p))
  /\ \A p \in participants: WF_vars(DetectFault(p))

\* Consistency: no two participants ever decide differently.
Agreement ==
  ~(\E p1, p2 \in participants:
       partDecision[p1] = commit /\ partDecision[p2] = abort)

\* A participant commits only if every participant voted yes.
CommitValid ==
  ~(\E p \in participants: partDecision[p] = commit /\ ~coordVotedYes)

\* A participant aborts only when it was forced by a no-vote or a crash.
AbortValid ==
  ~(\E p \in participants: partDecision[p] = abort /\ coordVotedYes
       /\ \A q \in participants: ~partFaulty[q] /\ ~coordFaulty)

\* Irreversibility: once committed or aborted, a participant never changes.
Irrevocable ==
  \A p \in participants:
    /\ (partDecision[p] = commit => partDecision'[p] = commit)
    /\ (partDecision[p] = abort => partDecision'[p] = abort)

\* Liveness (the blocking outcome): every participant either decides or some
\* node is known to have crashed; it is NOT a guarantee that all participants
\* decide -- a crashed coordinator can leave some undecided.
EventualDecisionOrFault ==
  <>(\A p \in participants: partDecision[p] # undecided \/ partFaulty[p] \/ coordFaulty)

====
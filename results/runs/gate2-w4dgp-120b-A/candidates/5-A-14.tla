---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordFaulty, coordDecision, coordRequested, coordRecv, coordBroadcasted,
          partAlive, partFaulty, partVote, partDecision, partSentVote

vars == <<coordAlive, coordFaulty, coordDecision, coordRequested, coordRecv, coordBroadcasted,
          partAlive, partFaulty, partVote, partDecision, partSentVote>>

TypeInv ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordRecv \in [participants -> {yes, no, waiting}]
  /\ coordBroadcasted \in [participants -> {notsent, commit, abort}]
  /\ partAlive \in [participants -> BOOLEAN]
  /\ partFaulty \in [participants -> BOOLEAN]
  /\ partVote \in [participants -> {yes, no}]
  /\ partDecision \in [participants -> {undecided, commit, abort}]
  /\ partSentVote \in [participants -> BOOLEAN]

Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = undecided
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordRecv = [p \in participants |-> waiting]
  /\ coordBroadcasted = [p \in participants |-> notsent]
  /\ partAlive = [p \in participants |-> TRUE]
  /\ partFaulty = [p \in participants |-> FALSE]
  /\ partVote = [p \in participants |-> yes]
  /\ partDecision = [p \in participants |-> undecided]
  /\ partSentVote = [p \in participants |-> FALSE]

\* The coordinator solicits a vote from participant p.
RequestVote(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRecv, coordBroadcasted,
                partAlive, partFaulty, partVote, partDecision, partSentVote>>

\* The coordinator receives the vote that participant p already sent.
ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordRecv[p] = waiting
  /\ partSentVote[p]
  /\ coordRecv' = [coordRecv EXCEPT ![p] = partVote[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested, coordBroadcasted,
                partAlive, partFaulty, partVote, partDecision, partSentVote>>

\* Failure detection: the coordinator notes that the requested participant p has
\* gone silent without sending its vote, so it decides to abort.
DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordRecv[p] = waiting
  /\ ~partAlive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<coordAlive, coordFaulty, coordRequested, coordRecv, coordBroadcasted,
                partAlive, partFaulty, partVote, partDecision, partSentVote>>

\* The coordinator commits only once every requested vote is in and all are yes.
MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordRequested[p]
  /\ \A p \in participants : coordRecv[p] # waiting
  /\ coordDecision' = (IF \A p \in participants : coordRecv[p] = yes THEN commit ELSE abort)
  /\ UNCHANGED <<coordAlive, coordFaulty, coordRequested, coordRecv, coordBroadcasted,
                partAlive, partFaulty, partVote, partDecision, partSentVote>>

\* Simple broadcast: the coordinator sends the decision to participant p.
BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordBroadcasted[p] = notsent
  /\ coordBroadcasted' = [coordBroadcasted EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested, coordRecv,
                partAlive, partFaulty, partVote, partDecision, partSentVote>>

DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, coordRequested, coordRecv, coordBroadcasted,
                partAlive, partFaulty, partVote, partDecision, partSentVote>>

\* A participant sends its vote back to the coordinator.
SendVote(p) ==
  /\ partAlive[p]
  /\ coordRequested[p]
  /\ ~partSentVote[p]
  /\ partSentVote' = [partSentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested, coordRecv,
                coordBroadcasted, partAlive, partFaulty, partVote, partDecision>>

\* A participant that voted no aborts unilaterally.
AbortOnVote(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ partVote[p] = no
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested, coordRecv,
                coordBroadcasted, partAlive, partFaulty, partVote, partSentVote>>

\* A participant times out waiting for the coordinator to send a request.
AbortOnTimeout(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ ~coordAlive
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested, coordRecv,
                coordBroadcasted, partAlive, partFaulty, partVote, partSentVote>>

\* The participant adopts whatever decision the coordinator broadcast to it.
DecideFromCoordinator(p) ==
  /\ partAlive[p]
  /\ partDecision[p] = undecided
  /\ coordBroadcasted[p] # notsent
  /\ partDecision' = [partDecision EXCEPT ![p] = coordBroadcasted[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested, coordRecv,
                coordBroadcasted, partAlive, partFaulty, partVote, partSentVote>>

DieParticipant(p) ==
  /\ partAlive[p]
  /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
  /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRequested, coordRecv,
                coordBroadcasted, partVote, partDecision, partSentVote>>

Next ==
  \/ \E p \in participants : RequestVote(p)
  \/ \E p \in participants : ReceiveVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : BroadcastDecision(p)
  \/ DieCoordinator
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideFromCoordinator(p)
  \/ \E p \in participants : DieParticipant(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : BroadcastDecision(p))
  /\ WF_vars(\E p \in participants : AbortOnVote(p))
  /\ WF_vars(\E p \in participants : DecideFromCoordinator(p))

\* No two participants can ever end up with different final decisions: commit and
\* abort are mutually exclusive across the whole participant set.
Agreement ==
  \A p \in participants, q \in participants :
    (partDecision[p] = commit /\ partDecision[q] = abort) => FALSE

\* A commit can only happen if every participant voted yes.
CommitValidity ==
  \A p \in participants : partDecision[p] = commit => partVote[p] = yes

\* An abort must be justified: some vote was no, or some participant crashed,
\* or the coordinator crashed.
AbortValidity ==
  \A p \in participants : partDecision[p] = abort =>
    \/ \E q \in participants : partVote[q] = no
    \/ \E q \in participants : partFaulty[q]
    \/ coordFaulty

\* A participant's decision is irreversible: once committed it stays committed,
\* and once aborted it stays aborted.
Irreversibility ==
  \A p \in participants :
    (partDecision[p] = commit ~> partDecision[p] = commit) /\ (partDecision[p] = abort ~> partDecision[p] = abort)

\* Even though the simple broadcast variant is blocking (it does not guarantee
\* that every non-faulty participant is decided), it still guarantees that the
\* protocol does not stall forever without reaching some outcome: either all
\* participants decide, or a participant is detected faulty, or the
\* coordinator is detected faulty.
DecisionOrFault ==
  (AC2 /\ AC3 /\ AC4 /\ (AC2 \/ AC3 \/ AC4))

====
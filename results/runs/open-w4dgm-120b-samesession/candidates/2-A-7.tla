---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-NB: Non-blocking atomic commitment protocol with reliable broadcast.
\* Submission node: participant; coordinator: coordinator.

VARIABLES prop, ack, coordDecision, coordAlive, coordFaulty, partFaulty, partDecision, partStage, forwarded

vars == <<prop, ack, coordDecision, coordAlive, coordFaulty, partFaulty, partDecision, partStage, forwarded>>

TypeOK ==
  /\ prop \in {yes, no}
  /\ ack \in {yes, no, undecided}
  /\ coordDecision \in {commit, abort, waiting}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ partFaulty \in [participants -> BOOLEAN]
  /\ partDecision \in [participants -> {commit, abort, undecided}]
  /\ partStage \in [participants -> {"voting", "ready"}]
  /\ \A p \in participants : forwarded[p] \in [participants -> {notsent, commit, abort}]

Init ==
  /\ prop = undecided
  /\ ack = undecided
  /\ coordDecision = waiting
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ partFaulty = [p \in participants |-> FALSE]
  /\ partDecision = [p \in participants |-> undecided]
  /\ partStage = [p \in participants |-> "voting"]
  /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator requests a broadcast by posting the agreed decision to a
\* participant's forwarding table entry (the broadcast itself may be slow).
Request ==
  /\ coordAlive
  /\ coordDecision = waiting
  /\ prop # undecided
  /\ ack = prop
  /\ coordDecision' = IF prop = yes THEN commit ELSE abort
  /\ UNCHANGED <<prop, ack, coordAlive, coordFaulty, partFaulty, partDecision, partStage, forwarded>>

GetVote(v) ==
  /\ coordAlive
  /\ prop = undecided
  /\ prop' = v
  /\ UNCHANGED <<ack, coordDecision, coordAlive, coordFaulty, partFaulty, partDecision, partStage, forwarded>>

\* Coordinator detects a participant has crashed for good.
DetectFault(p) ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ partFaulty[p]
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<prop, ack, coordDecision, coordAlive, partFaulty, partDecision, partStage, forwarded>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # waiting
  /\ forwarded[p][p] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED <<prop, ack, coordDecision, coordAlive, coordFaulty, partFaulty, partDecision, partStage>>

Die ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<prop, ack, coordDecision, coordFaulty, partFaulty, partDecision, partStage, forwarded>>

\* Participant receives a pre-decision broadcast by the coordinator.
PreDecide(p) ==
  /\ ~partFaulty[p]
  /\ forwarded[p][p] # notsent
  /\ partStage[p] = "voting"
  /\ partStage' = [partStage EXCEPT ![p] = "ready"]
  /\ UNCHANGED <<prop, ack, coordDecision, coordAlive, coordFaulty, partFaulty, partDecision, forwarded>>

\* Participant receives a pre-decision forwarded by another participant.
ForwardedPreDecide(p, q) ==
  /\ ~partFaulty[p]
  /\ forwarded[q][p] # notsent
  /\ partStage[p] = "voting"
  /\ partStage' = [partStage EXCEPT ![p] = "ready"]
  /\ UNCHANGED <<prop, ack, coordDecision, coordAlive, coordFaulty, partFaulty, partDecision, forwarded>>

\* Participant forwards its pre-decision to another participant that has not
\* yet received it.
Forward(p, q) ==
  /\ ~partFaulty[p]
  /\ partStage[p] = "ready"
  /\ forwarded[p][q] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][q] = IF coordDecision = commit THEN commit ELSE abort]
  /\ UNCHANGED <<prop, ack, coordDecision, coordAlive, coordFaulty, partFaulty, partDecision, partStage>>

\* Once a participant has forwarded to everybody, it finalizes its own decision.
Decide(p) ==
  /\ ~partFaulty[p]
  /\ partStage[p] = "ready"
  /\ \A q \in participants : forwarded[p][q] # notsent
  /\ partDecision' = [partDecision EXCEPT ![p] = IF coordDecision = commit THEN commit ELSE abort]
  /\ UNCHANGED <<prop, ack, coordDecision, coordAlive, coordFaulty, partFaulty, partStage, forwarded>>

\* A participant aborts when its coordinator is gone and no forward is in flight.
AbortOnTimeout(p) ==
  /\ ~partFaulty[p]
  /\ partDecision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : forwarded[q][p] = notsent
  /\ \A q \in participants : partFaulty[q] => forwarded[q][p] = notsent
  /\ partDecision' = [partDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<prop, ack, coordDecision, coordAlive, coordFaulty, partFaulty, partStage, forwarded>>

DieP(p) ==
  /\ ~partFaulty[p]
  /\ partFaulty' = [partFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<prop, ack, coordDecision, coordAlive, coordFaulty, partDecision, partStage, forwarded>>

Next ==
  \/ Request
  \/ \E v \in {yes, no} : GetVote(v)
  \/ \E p \in participants : DieP(p)
  \/ \E p \in participants : DetectFault(p)
  \/ \E p \in participants : Broadcast(p)
  \/ Die
  \/ \E p \in participants : PreDecide(p)
  \/ \E p, q \in participants : ForwardedPreDecide(p, q)
  \/ \E p, q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortOnTimeout(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Request)
  /\ \A p \in participants : WF_vars(PreDecide(p))
  /\ \A p \in participants, q \in participants : WF_vars(Forward(p, q))
  /\ \A p \in participants : WF_vars(Decide(p))
  /\ WF_vars(Die)
  /\ WF_vars(DieP(participants[1]))

\* No two participants may reach conflicting decisions.
Agreement ==
  \A p, q \in participants : (partDecision[p] = commit /\ partDecision[q] = abort) => FALSE

\* A commit requires unanimous yes votes.
CommitValidity ==
  \A p \in participants : (partDecision[p] = commit) => (prop = yes)

\* An abort is justified: some no vote, a faulty participant, or a faulty coordinator.
AbortValidity ==
  \A p \in participants :
    (partDecision[p] = abort) =>
      \/ ack = no
      \/ \E q \in participants : partFaulty[q]
      \/ coordFaulty

\* Decisions are irreversible: once made they never change.
Irrevocability ==
  \A p \in participants :
    /\ (partDecision[p] = commit) => (partDecision' = [partDecision EXCEPT ![p] = commit])
    /\ (partDecision[p] = abort) => (partDecision' = [partDecision EXCEPT ![p] = abort])

\* Every non-faulty participant eventually decides.
Termination ==
  \A p \in participants : (partFaulty[p] = FALSE) ~> (partDecision[p] # undecided)

TypeInvNB == TypeOK

====
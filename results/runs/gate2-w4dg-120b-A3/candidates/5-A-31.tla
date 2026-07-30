---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, requestSent, coordVote, sentCoord

vars == <<vote, alive, decision, faulty, sentVote, requestSent, coordVote, sentCoord>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants \cup {"coord"} -> {undecided, commit, abort}]
  /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ requestSent \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ sentCoord \in [participants -> {commit, abort, notsent}]

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
  /\ decision = [p \in participants \cup {"coord"} |-> undecided]
  /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ requestSent = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ sentCoord = [p \in participants |-> notsent]

\* Coordinator sends a vote request to a participant.
SendRequest(p) ==
  /\ alive["coord"]
  /\ ~requestSent[p]
  /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordVote, sentCoord>>

\* Coordinator receives a participant's vote.
RecvVote(p) ==
  /\ alive["coord"]
  /\ decision["coord"] = undecided
  /\ requestSent[p]
  /\ coordVote[p] = waiting
  /\ sentVote[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requestSent, sentCoord>>

\* Coordinator detects a participant fault before receiving its vote.
DetectFault(p) ==
  /\ alive["coord"]
  /\ decision["coord"] = undecided
  /\ requestSent[p]
  /\ coordVote[p] = waiting
  /\ ~alive[p]
  /\ decision' = [decision EXCEPT !["coord"] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requestSent, coordVote, sentCoord>>

\* Coordinator makes a commit/abort decision once all votes are in.
MakeDecision ==
  /\ alive["coord"]
  /\ decision["coord"] = undecided
  /\ \A p \in participants : coordVote[p] # waiting
  /\ decision' = [decision EXCEPT !["coord"] =
        IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requestSent, coordVote, sentCoord>>

\* Coordinator broadcasts its decision to a participant (simple broadcast).
SendCoord(p) ==
  /\ alive["coord"]
  /\ decision["coord"] # undecided
  /\ sentCoord[p] = notsent
  /\ sentCoord' = [sentCoord EXCEPT ![p] = decision["coord"]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requestSent, coordVote>>

CoordDie ==
  /\ alive["coord"]
  /\ alive' = [alive EXCEPT !["coord"] = FALSE]
  /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, requestSent, coordVote, sentCoord>>

\* Participant sends its vote to the coordinator.
SendVote(p) ==
  /\ alive[p]
  /\ requestSent[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, requestSent, coordVote, sentCoord>>

\* A participant unilaterally aborts upon voting no.
AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requestSent, coordVote, sentCoord>>

\* A participant aborts upon timeout (no request, coordinator dead).
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~requestSent[p]
  /\ ~alive["coord"]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requestSent, coordVote, sentCoord>>

\* A participant decides upon receiving the coordinator's broadcast.
DecideOnCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentCoord[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = sentCoord[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requestSent, coordVote, sentCoord>>

PartDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, requestSent, coordVote, sentCoord>>

\* Participant progress actions, excluded from death fairness assumptions.
PartProgress ==
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideOnCoord(p)

CoordProgress ==
  \/ \E p \in participants : SendRequest(p)
  \/ \E p \in participants : RecvVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : SendCoord(p)

Next ==
  \/ CoordProgress
  \/ PartProgress
  \/ CoordDie
  \/ \E p \in participants : PartDie(p)

\* Death actions are excluded from fairness assumptions.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CoordProgress)
  /\ WF_vars(PartProgress)

\* Safety: no two participants ever decide differently.
AC1 ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => p = q

\* Safety: a committed participant implies a unanimous yes vote.
AC2 == \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

\* Safety: an abort happened only because of a no vote, a faulty participant, or a faulty coordinator.
AC3 ==
  \A p \in participants :
    decision[p] = abort => (\E q \in participants : vote[q] = no \/ faulty[q]) \/ faulty["coord"]

\* Safety: a participant's decision is irreversible.
AC4 ==
  \A p \in participants :
    (decision[p] = commit => (decision' [p] = commit)) /\ (decision[p] = abort => (decision' [p] = abort))

\* Liveness: the protocol always eventually resolves or fails.
EventualResolveOrFail ==
  <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ faulty["coord"])

====
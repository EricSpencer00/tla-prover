---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES alive, decision, broadcast, coordVote, coordDecision, coordAlive

vars == <<alive, decision, broadcast, coordVote, coordDecision, coordAlive>>

TypeInv ==
  /\ alive \in [participants -> {"alive", "faulty"}]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ broadcast \in [participants -> {notsent, commit, abort}]
  /\ coordVote \in [participants -> {waiting, yes, no}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in {"alive", "faulty"}
  /\ \E v \in {yes, no} : \E p \in participants : alive[p] = "alive" /\ decision[p] = undecided
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in {"alive", "faulty"}

Init ==
  /\ alive = [p \in participants |-> "alive"]
  /\ decision = [p \in participants |-> undecided]
  /\ broadcast = [p \in participants |-> notsent]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordDecision = undecided
  /\ coordAlive = "alive"
  /\ \E v \in {yes, no} : \E p \in participants : alive[p] = "alive" /\ decision[p] = undecided

SendRequest(p) ==
  /\ coordAlive = "alive"
  /\ coordVote[p] = waiting
  /\ coordVote' = [coordVote EXCEPT ![p] = waiting]
  /\ UNCHANGED <<alive, decision, broadcast, coordDecision, coordAlive>>

ReceiveVote(p) ==
  /\ coordAlive = "alive"
  /\ coordDecision = undecided
  /\ \A q \in participants : coordVote[q] \in {yes, no}
  /\ coordVote[p] = waiting
  /\ alive[p] = "alive"
  /\ coordVote' = [coordVote EXCEPT ![p] = coordVote[p]]
  /\ UNCHANGED <<alive, decision, broadcast, coordDecision, coordAlive>>

DetectFault(p) ==
  /\ coordAlive = "alive"
  /\ coordDecision = undecided
  /\ \A q \in participants : coordVote[q] \in {yes, no}
  /\ coordVote[p] = waiting
  /\ alive[p] = "faulty"
  /\ coordDecision' = abort
  /\ UNCHANGED <<alive, decision, broadcast, coordVote, coordAlive>>

MakeDecision ==
  /\ coordAlive = "alive"
  /\ coordDecision = undecided
  /\ \A q \in participants : coordVote[q] \in {yes, no}
  /\ coordDecision' = IF \A q \in participants : coordVote[q] = yes THEN commit ELSE abort
  /\ UNCHANGED <<alive, decision, broadcast, coordVote, coordAlive>>

BroadcastCoord(p) ==
  /\ coordAlive = "alive"
  /\ coordDecision # undecided
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<alive, decision, coordVote, coordDecision, coordAlive>>

CoordDie ==
  /\ coordAlive = "alive"
  /\ coordAlive' = "faulty"
  /\ UNCHANGED <<alive, decision, broadcast, coordVote, coordDecision>>

SendVote(p) ==
  /\ alive[p] = "alive"
  /\ coordAlive = "alive"
  /\ broadcast[p] = notsent
  /\ coordVote[p] = waiting
  /\ coordVote' = [coordVote EXCEPT ![p] = IF alive[p] = "alive" THEN yes ELSE no]
  /\ UNCHANGED <<alive, decision, broadcast, coordDecision, coordAlive>>

AbortOnVote(p) ==
  /\ alive[p] = "alive"
  /\ decision[p] = undecided
  /\ coordVote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<alive, broadcast, coordVote, coordDecision, coordAlive>>

AbortOnTimeout(p) ==
  /\ alive[p] = "alive"
  /\ decision[p] = undecided
  /\ coordAlive = "faulty"
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<alive, broadcast, coordVote, coordDecision, coordAlive>>

DecideBasedOnCoord(p) ==
  /\ alive[p] = "alive"
  /\ decision[p] = undecided
  /\ broadcast[p] \in {commit, abort}
  /\ decision' = [decision EXCEPT ![p] = broadcast[p]]
  /\ UNCHANGED <<alive, broadcast, coordVote, coordDecision, coordAlive>>

ParticipantDie(p) ==
  /\ alive[p] = "alive"
  /\ alive' = [alive EXCEPT ![p] = "faulty"]
  /\ UNCHANGED <<decision, broadcast, coordVote, coordDecision, coordAlive>>

Next ==
  \/ MakeDecision
  \/ CoordDie
  \/ \E p \in participants :
       SendRequest(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ BroadcastCoord(p)
         \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p)
         \/ DecideBasedOnCoord(p) \/ ParticipantDie(p)

Spec == Init /\ [][Next]_vars

\* SAFETY: Agreement (no two participants decide differently) and decidability
\* (commit only on unanimous yes, abort otherwise).
Agreement ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitOnlyOnUnanimousYes ==
  \A p \in participants : decision[p] = commit => (\A q \in participants : coordVote[q] = yes)

AbortOnlyOnNoVoteOrFault ==
  \A p \in participants : decision[p] = abort =>
    (\E q \in participants : coordVote[q] = no) \/ (\E q \in participants : alive[q] = "faulty") \/ coordAlive = "faulty"

Irrevocability ==
  \A p \in participants :
    /\ (decision[p] = commit => decision' = [decision EXCEPT ![p] = commit])
    /\ (decision[p] = abort => decision' = [decision EXCEPT ![p] = abort])
    /\ UNCHANGED <<alive, broadcast, coordVote, coordDecision, coordAlive>>

\* LIVENESS: the protocol eventually resolves or detects a failure. Termination
\* is NOT guaranteed in this blocking variant; the coordinator can crash mid-broadcast.
EventualDecision == <>(\E p \in participants : decision[p] # undecided)
====
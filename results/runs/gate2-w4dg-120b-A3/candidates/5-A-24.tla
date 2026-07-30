---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
  participants,
  yes,
  no,
  undecided,
  commit,
  abort,
  waiting,
  notsent

VARIABLES
  vote,
  alive,
  decision,
  faulty,
  sent,
  requested,
  recv,
  broadcast,
  coordDecision,
  coordAlive,
  coordFaulty

vars == <<vote, alive, decision, faulty, sent, requested, recv,
          broadcast, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sent \in [participants -> BOOLEAN]
  /\ requested \in [participants -> BOOLEAN]
  /\ recv \in [participants -> {yes, no, waiting}]
  /\ broadcast \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sent = [p \in participants |-> FALSE]
  /\ requested = [p \in participants |-> FALSE]
  /\ recv = [p \in participants |-> waiting]
  /\ broadcast = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator sends a vote request to a participant.
SendRequest(p) ==
  /\ coordAlive
  /\ ~requested[p]
  /\ requested' = [requested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, recv,
                broadcast, coordDecision, coordAlive, coordFaulty>>

\* The coordinator receives a vote from a participant.
RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants : requested[q]
  /\ recv[p] = waiting
  /\ sent[p]
  /\ recv' = [recv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, requested,
                broadcast, coordDecision, coordAlive, coordFaulty>>

\* The coordinator detects a participant fault and aborts.
DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants : requested[q]
  /\ recv[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, requested,
                recv, broadcast, coordAlive, coordFaulty>>

\* The coordinator makes its commit/abort decision once all votes are in.
MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : recv[p] # waiting
  /\ coordDecision' = IF \A p \in participants : recv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, requested,
                recv, broadcast, coordAlive, coordFaulty>>

\* The coordinator broadcasts its decision to a participant (simple broadcast).
Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, requested,
                recv, coordDecision, coordAlive, coordFaulty>>

DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, requested,
                recv, broadcast, coordDecision>>

\* A participant sends its vote to the coordinator.
SendVote(p) ==
  /\ alive[p]
  /\ requested[p]
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, requested, recv,
                broadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant aborts unilaterally on its own no vote.
AbortOnNo(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sent[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, requested, recv,
                broadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant aborts after the coordinator dies without a request.
AbortOnCoordTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ broadcast[p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, requested, recv,
                broadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant adopts the decision broadcast by the coordinator.
DecideFromBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcast[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, sent, requested, recv,
                broadcast, coordDecision, coordAlive, coordFaulty>>

DieParticipant(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sent, requested, recv,
                broadcast, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants :
       SendRequest(p) \/ RecvVote(p) \/ DetectFault(p) \/ Broadcast(p)
         \/ SendVote(p) \/ AbortOnNo(p) \/ AbortOnCoordTimeout(p)
         \/ DecideFromBroadcast(p) \/ DieParticipant(p)
  \/ MakeDecision
  \/ DieCoordinator

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendVote(ANY p \in participants))
  /\ WF_vars(AbortOnNo(ANY p \in participants))
  /\ WF_vars(DecideFromBroadcast(ANY p \in participants))
  /\ WF_vars(MakeDecision)

\* No two participants ever decide differently.
Agreement ==
  \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE

\* A commit can only happen if everyone voted yes.
CommitValidity ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

\* An abort must be backed by a no vote or a fault.
AbortValidity ==
  \A p \in participants :
    decision[p] = abort =>
      \/ (\E q \in participants : vote[q] = no)
      \/ (\E q \in participants : faulty[q])
      \/ coordFaulty

\* Decisions are irreversible.
Irreversible ==
  \A p \in participants :
    /\ (decision[p] = commit => decision[p] = commit)
    /\ (decision[p] = abort => decision[p] = abort)

TypeInv == TypeOK

DecideEventually ==
  <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ coordFaulty)

====
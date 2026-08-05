---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, requested, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentVote, requested, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ requested \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ broadcasted \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ \E v \in [participants -> {yes, no}]:
       vote = v
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ requested = [p \in participants |-> FALSE]
  /\ recvVote = [p \in participants |-> waiting]
  /\ broadcasted = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendRequest(p) ==
  /\ coordAlive
  /\ ~requested[p]
  /\ requested' = [requested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants: requested[q]
  /\ recvVote[p] = waiting
  /\ sentVote[p]
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested, broadcasted, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A q \in participants: requested[q]
  /\ recvVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested, recvVote, broadcasted, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants: recvVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants: recvVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested, recvVote, broadcasted, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ broadcasted[p] = notsent
  /\ broadcasted' = [broadcasted EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested, recvVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, requested, recvVote, broadcasted, coordDecision>>

SendVote(p) ==
  /\ alive[p]
  /\ requested[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, requested, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~requested[p]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcasted[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcasted[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, requested, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, requested, recvVote, broadcasted, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants: SendRequest(p)
  \/ \E p \in participants: ReceiveVote(p)
  \/ \E p \in participants: DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants: BroadcastDecision(p)
  \/ CoordDie
  \/ \E p \in participants: SendVote(p)
  \/ \E p \in participants: AbortOnVote(p)
  \/ \E p \in participants: AbortOnTimeout(p)
  \/ \E p \in participants: DecideOnBroadcast(p)
  \/ \E p \in participants: ParticipantDie(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants: WF_vars(SendVote(p))
  /\ \A p \in participants: WF_vars(AbortOnVote(p))
  /\ \A p \in participants: WF_vars(DecideOnBroadcast(p))
  /\ \A p \in participants: WF_vars(AbortOnTimeout(p))
  /\ \A p \in participants: WF_vars(SendRequest(p))
  /\ \A p \in participants: WF_vars(ReceiveVote(p))
  /\ \A p \in participants: WF_vars(DetectFault(p))
  /\ WF_vars(MakeDecision)

Agreement ==
  \A p, q \in participants: ~(decision[p] = commit /\ decision[q] = abort)

CommitValidity ==
  \A p \in participants: decision[p] = commit => (\A q \in participants: vote[q] = yes)

AbortValidity ==
  \A p \in participants: decision[p] = abort =>
    (\E q \in participants: vote[q] = no \/ faulty[q] \/ coordFaulty)

Irrevocability ==
  \A p \in participants: (decision[p] = commit => [][decision[p] = commit]_(vars)) /\ (decision[p] = abort => [][decision[p] = abort]_(vars))

EventualDecision ==
  <>(\A p \in participants: decision[p] # undecided \/ faulty[p] \/ coordFaulty)

====
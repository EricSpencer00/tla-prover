---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME participants # {}

VARIABLES vote, alive, decision, faulty, sent, cstate, predec, fwd

vars == <<vote, alive, decision, faulty, sent, cstate, predec, fwd>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ sent \in [participants -> BOOLEAN]
  /\ cstate \in {"request", "vote", "broadcast", "decision", "dead", "abort"}
  /\ predec \in [participants -> {waiting, commit, abort}]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> no]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ sent = [p \in participants |-> FALSE]
  /\ cstate = "request"
  /\ predec = [p \in participants |-> waiting]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ cstate = "request"
  /\ cstate' = "vote"
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, predec, fwd>>

GetVote(p) ==
  /\ cstate = "vote"
  /\ alive[p]
  /\ ~sent[p]
  /\ \E v \in {yes, no}:
       /\ vote' = [vote EXCEPT ![p] = v]
       /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, cstate, predec, fwd>>

Detect ==
  /\ cstate = "vote"
  /\ \E p \in participants: ~alive[p] /\ ~decision[p]
  /\ cstate' = "broadcast"
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, predec, fwd>>

MakeDecision ==
  /\ cstate \in {"vote", "broadcast"}
  /\ cstate' = "decision"
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, predec, fwd>>

Broadcast ==
  /\ cstate = "decision"
  /\ cstate' = "request"
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, predec, fwd>>

Die ==
  /\ \E p \in participants:
       /\ alive[p]
       /\ alive' = [alive EXCEPT ![p] = FALSE]
       /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, sent, cstate, predec, fwd>>

PreDecFromCoordinator(p) ==
  /\ alive[p]
  /\ predec[p] = waiting
  /\ cstate = "decision"
  /\ predec' = [predec EXCEPT ![p] = cstate]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, cstate, fwd>>

PreDecFromRelay(p) ==
  /\ alive[p]
  /\ predec[p] = waiting
  /\ \E q \in participants:
       /\ q # p
       /\ fwd[q][p] # notsent
       /\ predec' = [predec EXCEPT ![p] = fwd[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, cstate, fwd>>

Forward(p) ==
  /\ alive[p]
  /\ predec[p] # waiting
  /\ \E q \in participants:
       /\ q # p
       /\ fwd[p][q] = notsent
       /\ fwd' = [fwd EXCEPT ![p][q] = predec[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent, cstate, predec>>

Decide(p) ==
  /\ alive[p]
  /\ predec[p] # waiting
  /\ \A q \in participants \ {p}: fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = predec[p]]
  /\ UNCHANGED <<vote, alive, faulty, sent, cstate, predec, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ cstate = "dead"
  /\ \A q \in participants: ~alive[q] => fwd[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ predec' = [predec EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, cstate, fwd>>

Next ==
  \/ SendRequest
  \/ \E p \in participants: GetVote(p) \/ PreDecFromCoordinator(p) \/ PreDecFromRelay(p)
  \/ \E p \in participants: Forward(p) \/ Decide(p) \/ AbortOnTimeout(p)
  \/ Detect \/ MakeDecision \/ Broadcast
  \/ Die

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: GetVote(p))
  /\ WF_vars(\E p \in participants: Forward(p))
  /\ WF_vars(\E p \in participants: Decide(p))
  /\ WF_vars(\E p \in participants: AbortOnTimeout(p))

AC1 == \A p1, p2 \in participants: ~(decision[p1] = commit /\ decision[p2] = abort)

AC2 == (\E p \in participants: vote[p] = no) => (\A p \in participants: decision[p] = abort)

AC3 == (\E p \in participants: decision[p] = abort) => (\A p \in participants: vote[p] = yes \/ p \in faulty \/ cstate = "dead")

AC4 == \A p \in participants: (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

AC3Liveness == <>(\A p \in participants: decision[p] # undecided \/ cstate = "dead" \/ faulty # {})

AC5 == \A p \in participants: (p \notin faulty /\ cstate # "dead") ~> (decision[p] # undecided)

PropertySet == {AC1, AC2, AC3, AC4, AC3Liveness, AC5}

====
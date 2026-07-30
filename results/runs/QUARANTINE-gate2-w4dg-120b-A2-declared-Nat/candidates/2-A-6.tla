---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voted, tx, coordinator, cstate, fwd

vars == <<pstate, alive, decision, faulty, voted, tx, coordinator, cstate, fwd>>

TypeInvNB ==
  /\ pstate \in [participants -> {undecided, yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ tx \in [participants -> {waiting, yes, no}]
  /\ coordinator \in participants
  /\ cstate \in {waiting, yes, no}
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitFwd ==
  [q \in participants |-> [r \in participants |-> notsent]]

InitNB ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ tx = [p \in participants |-> waiting]
  /\ coordinator \in participants
  /\ cstate = waiting
  /\ fwd = InitFwd

SendRequest(q) ==
  /\ alive[coordinator] /\ cstate = waiting /\ alive[q] /\ ~voted[q]
  /\ tx' = [tx EXCEPT ![q] = waiting]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, coordinator, cstate, fwd>>

GetVote(q, v) ==
  /\ alive[q] /\ cstate = waiting /\ ~voted[q]
  /\ tx' = [tx EXCEPT ![q] = v]
  /\ voted' = [voted EXCEPT ![q] = TRUE]
  /\ UNCHANGED <<pstate, alive, decision, faulty, coordinator, cstate, fwd>>

DetectFault ==
  /\ alive[coordinator]
  /\ \E q \in participants : cstate = waiting /\ ~alive[q] /\ tx[q] = waiting
  /\ faulty' = [faulty EXCEPT ![coordinator] = TRUE]
  /\ UNCHANGED <<pstate, alive, decision, voted, tx, coordinator, cstate, fwd>>

Broadcast(v) ==
  /\ alive[coordinator] /\ cstate = waiting
  /\ cstate' = v
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, tx, coordinator, fwd>>

PreDecideFromCoordinator(p) ==
  /\ alive[p] /\ decision[p] = undecided /\ tx[p] = cstate
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = cstate]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, tx, coordinator, cstate>>

PreDecideFromFwd(p) ==
  /\ alive[p] /\ decision[p] = undecided
  /\ \E q \in participants :
       /\ fwd[q][p] # notsent
       /\ fwd[p][p] = notsent
       /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, tx, coordinator, cstate>>

ForwardDecision(p, r) ==
  /\ alive[p] /\ decision[p] = undecided /\ fwd[p][p] # notsent
  /\ fwd[p][r] = notsent
  /\ fwd' = [fwd EXCEPT ![p][r] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, tx, coordinator, cstate>>

Decide(p) ==
  /\ alive[p] /\ decision[p] = undecided
  /\ \A r \in participants : fwd[p][r] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, faulty, voted, tx, coordinator, cstate, fwd>>

Die(p) ==
  /\ alive[p] /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, voted, tx, coordinator, cstate, fwd>>

NextNB ==
  \/ \E q \in participants : SendRequest(q) \/ GetVote(q, yes) \/ GetVote(q, no)
  \/ DetectFault
  \/ Broadcast(commit) \/ Broadcast(abort)
  \/ \E p \in participants :
       \/ PreDecideFromCoordinator(p) \/ PreDecideFromFwd(p) \/ Decide(p)
       \/ \E r \in participants : ForwardDecision(p, r)
       \/ Die(p)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(\E p \in participants : PreDecideFromCoordinator(p))
  /\ WF_vars(\E p \in participants : PreDecideFromFwd(p))
  /\ WF_vars(\E p \in participants, r \in participants : ForwardDecision(p, r))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E q \in participants : SendRequest(q))
  /\ WF_vars(\E q \in participants, v \in {yes, no} : GetVote(q, v))
  /\ WF_vars(Broadcast(commit) \/ Broadcast(abort))

Ac1 == ~ \E p, q \in participants : decision[p] = commit /\ decision[q] = abort

Ac2 == (\E p \in participants : decision[p] = commit) => \A q \in participants : pstate[q] = yes

Ac3 == (\E p \in participants : decision[p] = abort) =>
         \/ \E q \in participants : pstate[q] = no
         \/ \E q \in participants : faulty[q]
         \/ faulty[coordinator]

Ac4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~>
         (decision[p] = commit \/ decision[p] = abort)

Ac3Liveness == <>(\A p \in participants : decision[p] # undecided \/ \E q \in participants : faulty[q] \/ faulty[coordinator])

Ac5 == \A p \in participants : (decision[p] = undecided) ~> (decision[p] = commit \/ decision[p] = abort)

====
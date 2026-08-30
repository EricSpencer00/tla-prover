---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voteSent, ptable

vars == <<pstate, alive, decision, faulty, voteSent, ptable>>

TypeInvNB ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, waiting}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ ptable \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ ptable = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator: broadcast the decision to participant p.
Broad(p, d) ==
  /\ \A q \in participants : ptable[p][q] = notsent
  /\ ptable' = [ptable EXCEPT ![p] = [q \in participants |-> IF q = p THEN d ELSE notsent]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent>>

Decide(p) ==
  /\ \A q \in participants : ptable[p][q] # notsent
  /\ decision[p] = waiting
  /\ decision' = [decision EXCEPT ![p] = ptable[p][p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, ptable>>

\* A participant receives a pre-decision broadcast from the coordinator.
PreDecideCoord(p) ==
  /\ alive[p]
  /\ pstate[p] = undecided
  /\ ptable[p][p] # notsent
  /\ pstate' = [pstate EXCEPT ![p] = ptable[p][p]]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, ptable>>

\* A participant receives a pre-decision forwarded by another participant.
PreDecideFwd(p) ==
  /\ alive[p]
  /\ pstate[p] = undecided
  /\ (\E q \in participants : q # p /\ ptable[q][p] # notsent)
  /\ pstate' = [pstate EXCEPT ![p] = CHOOSE q \in participants : q # p /\ ptable[q][p] # notsent]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, ptable>>

\* Forward a pre-decision to another participant.
Forward(p, q) ==
  /\ alive[p]
  /\ pstate[p] # undecided
  /\ ptable[p][q] = notsent
  /\ ptable' = [ptable EXCEPT ![p][q] = pstate[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent>>

\* Abort when the coordinator is gone and no decision is in flight.
DecideAbort(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ pstate[p] = undecided
  /\ \A q \in participants : ptable[p][q] = notsent
  /\ (~ alive[CHOOSE q \in participants : TRUE])
  /\ (\A q \in participants : alive[q] => pstate[q] = undecided)
  /\ (\A q \in participants : (\A r \in participants : alive[r] => ptable[r][q] = notsent))
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, ptable>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, voteSent, ptable>>

Next ==
  \/ \E p \in participants, q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p) \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ DecideAbort(p) \/ Die(p)

SpecNB == Init /\ [][Next]_vars

\* Every non-faulty participant eventually reaches a decision.
DecideEventually ==
  \A p \in participants : (alive[p] /\ ~ faulty[p]) ~> (decision[p] # waiting)

====
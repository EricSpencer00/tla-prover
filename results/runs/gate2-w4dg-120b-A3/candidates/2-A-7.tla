---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, faulty, decision, alive, coordinator, pdecision, forwarded

vars == <<vote, faulty, decision, alive, coordinator, pdecision, forwarded>>

Entry == {notsent, commit, abort}

RECURSIVE AllForward(_, _)
AllForward(f, S) ==
  IF S = {} THEN TRUE
  ELSE LET p == CHOOSE x \in S : TRUE
       IN \A q \in S : f[p][q] # notsent /\ AllForward(f, S \ {p})

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ faulty \subseteq participants
  /\ decision \in [participants -> {deciding, commit, abort}]
  /\ alive \in [participants -> BOOLEAN]
  /\ coordinator \in [alive: BOOLEAN, faulty: BOOLEAN, decision: {commit, abort, waiting}]
  /\ pdecision \in {undecided, commit, abort}
  /\ forwarded \in [participants -> [participants -> Entry]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ decision = [p \in participants |-> deciding]
  /\ alive = [p \in participants |-> TRUE]
  /\ coordinator = [alive |-> TRUE, faulty |-> FALSE, decision |-> waiting]
  /\ pdecision = undecided
  /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

SendVote(p) ==
  /\ alive[p] /\ vote[p] = undecided
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED <<faulty, decision, alive, coordinator, pdecision, forwarded>>

PreDecideCoord(p) ==
  /\ alive[p] /\ forwarded[p][p] = notsent
  /\ coordinator.decision \in {commit, abort}
  /\ forwarded' = [forwarded EXCEPT ![p][p] = coordinator.decision]
  /\ UNCHANGED <<vote, faulty, decision, alive, coordinator, pdecision>>

PreDecideForward(p) ==
  /\ alive[p] /\ forwarded[p][p] = notsent
  /\ coordinator.decision = waiting
  /\ \E q \in participants :
       /\ alive[q]
       /\ forwarded[q][p] # notsent
       /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[q][p]]
  /\ UNCHANGED <<vote, faulty, decision, alive, coordinator, pdecision>>

Forward(p, q) ==
  /\ alive[p] /\ forwarded[p][p] # notsent /\ forwarded[p][q] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
  /\ UNCHANGED <<vote, faulty, decision, alive, coordinator, pdecision>>

Decide(p) ==
  /\ alive[p] /\ decision[p] = deciding /\ forwarded[p][p] # notsent
  /\ \A q \in participants : forwarded[p][q] = forwarded[p][p]
  /\ decision' = [decision EXCEPT ![p] = forwarded[p][p]]
  /\ UNCHANGED <<vote, faulty, alive, coordinator, pdecision, forwarded>>

AbortOnTimeout(p) ==
  /\ alive[p] /\ decision[p] = deciding
  /\ (coordinator.faulty \/ ~ coordinator.alive)
  /\ \A q \in participants : coordinator.alive => forwarded[q][p] = notsent
  /\ \A q \in participants : q \in faulty => \A r \in participants : forwarded[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, faulty, alive, coordinator, pdecision, forwarded>>

Die ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED <<vote, faulty, decision, alive, pdecision, forwarded>>

CoordinatorActions ==
  \/ Die

ParticipantActions ==
  \/ \E p \in participants : SendVote(p) \/ PreDecideCoord(p) \/ PreDecideForward(p) \/ Decide(p) \/ AbortOnTimeout(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)

Next ==
  \/ CoordinatorActions
  \/ ParticipantActions

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : PreDecideCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideForward(p))
  /\ WF_vars(\E p, q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

NoConflictingDecisions ==
  ~ (\E p, q \in participants : decision[p] = commit /\ decision[q] = abort)

CommitRequiresAllYes ==
  (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

AbortRequiresBad == (\E p \in participants : decision[p] = abort) => (pdecision = abort \/ coordinator.faulty)

DecisionsAreIrreversible ==
  \A p \in participants : \A d \in {commit, abort} : (decision[p] = d) ~> (decision[p] = d)

TerminateOrCrash ==
  <>(\A p \in participants : decision[p] # deciding) \/ (\E p \in participants : faulty[p]) \/ coordinator.faulty

NonFaultyTerminate ==
  \A p \in participants : (~faulty[p] /\ alive[p]) ~> (decision[p] # deciding)

Properties == TerminateOrCrash /\ NonFaultyTerminate

TypeInvNB == TypeOK /\ NoConflictingDecisions /\ CommitRequiresAllYes /\ AbortRequiresBad /\ DecisionsAreIrreversible

====
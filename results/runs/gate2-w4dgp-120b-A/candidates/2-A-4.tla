---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

\* Non-Blocking Atomic Commitment (ACP-NB) builds on the simple broadcast
\* protocol (ACP-SB) by adding a reliable broadcast: when a participant
\* receives a decision, it forwards it to all other participants before
\* delivering it locally.  This ensures that even if the coordinator
\* crashes mid-broadcast, participants can still drive the decision to
\* termination by peer forwarding, which is exactly what the non-blocking
\* termination property (every non-faulty participant eventually decides)
\* relies on.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME waiting # undecided /\ commit # abort /\ notsent # commit /\ notsent # abort

VARIABLES vote, alive, decision, faulty, voteSent, coordinator, fwd

vars == << vote, alive, decision, faulty, voteSent, coordinator, fwd >>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordinator \in {waiting, commit, abort, broken}
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordinator = waiting
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* A participant adopts a pre-decision either from the coordinator broadcast
\* or from a peer's forwarding message, but only while it is still alive.
PredecideByCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordinator \in {commit, abort}
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordinator]
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent, coordinator >>

PredecideByForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ (\E q \in participants : q # p /\ fwd[q][p] # notsent)
  /\ fwd' = [fwd EXCEPT ![p][p] = CHOOSE q \in participants : q # p /\ fwd[q][p] # notsent]
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent, coordinator >>

\* Forwarding is the reliable-broadcast step: a participant can forward its
\* pre-decision to any other participant, exactly once per recipient.
Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED << vote, alive, decision, faulty, voteSent, coordinator >>

DecideNB(p) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED << vote, alive, faulty, voteSent, coordinator, fwd >>

\* Abort on timeout now requires that no surviving participant is stranded
\* waiting on the coordinator AND no dead participant could still rescue
\* them through a queued forwarding message.  Only then does timeout-triggered
\* abort fire, which is what guarantees every non-faulty participant still
\* has a live path to a decision.
AbortOnTimeoutNB(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordinator = broken
  /\ \A q \in participants : alive[q] => fwd[q][p] = notsent
  /\ \A q \in participants : ~alive[q] => (\A r \in participants : fwd[q][r] = notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, voteSent, coordinator, fwd >>

DieNB(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << vote, decision, voteSent, coordinator, fwd >>

NextNB ==
  \/ DecideNB(p) \/ AbortOnTimeoutNB(p) \/ DieNB(p) \/ PredecideByCoordinator(p) \/ PredecideByForward(p) \/ \E q \in participants : Forward(p, q)
  \/ \E p \in participants : \E a \in {waiting, commit, abort, broken} : CoordinatorDecide(a) \/ CoordinatorBroadcast(a) \/ CoordinatorDie(a)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(\E p \in participants : DecideNB(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeoutNB(p))
  /\ WF_vars(\E p \in participants : DieNB(p))
  /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : PredecideByCoordinator(p))
  /\ WF_vars(\E p \in participants : PredecideByForward(p))
  /\ WF_vars(CoordinatorDecide(waiting))
  /\ WF_vars(CoordinatorBroadcast(waiting))
  /\ WF_vars(CoordinatorDie(waiting))

\* Safety: agreement, plus validity of each outcome.
AC1 == ~(commit \in {decision[p] : p \in participants} /\ abort \in {decision[p] : p \in participants})

AC2 == commit \in {decision[p] : p \in participants} => (\A p \in participants : vote[p] = yes)

AC3 == abort \in {decision[p] : p \in participants} => (no \in {vote[p] : p \in participants} \/ \E p \in participants : faulty[p] \/ coordinator = broken)

AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

\* Liveness: the non-blocking property is driven by the reliable broadcast --
\* every non-faulty participant eventually decides, regardless of coordinator
\* failures or message ordering.
LivenessNB == \A p \in participants : ~faulty[p] ~> (decision[p] = commit \/ decision[p] = abort)

====
---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordState, coordDecision, coordAlive, coordFaulty, votes, alive, decision, fwd

vars == <<coordState, coordDecision, coordAlive, coordFaulty, votes, alive,
         decision, fwd>>

\* fwd[p][q] is participant p's forwarding table entry for participant q: notsent,
\* commit, or abort. The p,p entry is the pre-decision p received.
Bump(s) == IF s = commit THEN abort ELSE commit

TypeInvNB ==
  /\ coordState \in {waiting, commit, abort}
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ votes \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitState ==
  /\ coordState = waiting
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ votes = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendVote(p) ==
  /\ alive[p]
  /\ votes[p] = undecided
  /\ \E v \in {yes, no} : votes' = [votes EXCEPT ![p] = v]
  /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty,
                 alive, decision, fwd>>

CoordinatorDecides ==
  /\ coordAlive
  /\ coordState = waiting
  /\ \A p \in participants : votes[p] # undecided
  /\ coordState' = IF \A p \in participants : votes[p] = yes THEN commit ELSE abort
  /\ coordDecision' = IF \A p \in participants : votes[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<coordAlive, coordFaulty, votes, alive, decision, fwd>>

BroadcastDecision ==
  /\ coordAlive
  /\ coordState \in {commit, abort}
  /\ coordDecision' = coordState
  /\ UNCHANGED <<coordState, coordAlive, coordFaulty, votes, alive,
                 decision, fwd>>

PreDecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordAlive
  /\ fwd[p][p] = notsent
  /\ coordDecision # undecided
  /\ fwd' = [fwd EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty,
                 votes, alive, decision>>

PreDecideFromPeer(p, q) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty,
                 votes, alive, decision>>

Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty,
                 votes, alive, decision>>

DecideNB(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] # notsent
  /\ \A q \in participants \ {p} : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty,
                 votes, alive, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : alive[q] => fwd[q][p] = notsent
  /\ \A d \in participants : ~alive[d] => \A q \in participants : alive[q] => fwd[d][q] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordState, coordDecision, coordAlive, coordFaulty,
                 votes, alive, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ coordAlive' = IF coordAlive /\ coordState = waiting THEN FALSE ELSE coordAlive
  /\ coordFaulty' = IF coordAlive /\ coordState = waiting THEN TRUE ELSE coordFaulty
  /\ UNCHANGED <<coordState, coordDecision, votes, decision, fwd>>

Next ==
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : PreDecideFromCoordinator(p)
  \/ \E p \in participants, q \in participants : PreDecideFromPeer(p, q)
  \/ \E p \in participants, q \in participants : Forward(p, q)
  \/ \E p \in participants : DecideNB(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : Die(p)
  \/ CoordinatorDecides
  \/ BroadcastDecision

SpecNB ==
  /\ InitState
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : PreDecideFromCoordinator(p))
  /\ WF_vars(\E p \in participants, q \in participants : PreDecideFromPeer(p, q))
  /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : DecideNB(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

\* No two participants reach different decisions.
AC1 ==
  \A p, q \in participants :
    ~(decision[p] = commit /\ decision[q] = abort)

\* A commit implies the unanimous yes vote.
AC2 ==
  (\E p \in participants : decision[p] = commit) =>
    (\A p \in participants : votes[p] = yes)

\* An abort is always justified: a no vote, a faulty participant, or a dead coordinator.
AC3 ==
  (\E p \in participants : decision[p] = abort) =>
    \/ \E p \in participants : votes[p] = no
       \/ \E p \in participants : ~alive[p]
       \/ coordFaulty

\* Decisions are irreversible.
Irrevocable ==
  \A p \in participants :
    (decision[p] = commit \/ decision[p] = abort) =>
      (decision[p] = commit \/ decision[p] = abort)

\* Either everyone decides, or somebody has failed.
AC3Liveness ==
  <>(\A p \in participants : decision[p] # undecided) \/ coordFaulty

\* Every non-faulty participant eventually decides -- the non-blocking guarantee.
AC5 ==
  \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

Properties == <<AC1, AC2, AC3, Irrevocable, AC3Liveness, AC5>>

====
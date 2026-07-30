---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding status for a participant's reliable broadcast table entry:
\* not-sent means no pre-decision received, commit means pre-decision is commit,
\* abort means pre-decision is abort.
VARIABLES vote, alive, decision, faulty, voted, coordState, phase, forward

vars == <<vote, alive, decision, faulty, voted, coordState, phase, forward>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ coordState \in {waiting, "request", "vote", "broadcast", "decide", "dead"}
  /\ phase \in {undecided, commit, abort}
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ vote = [p \in participants |-> yes]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ coordState = waiting
  /\ phase = undecided
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

DecideConsistent ==
  \A p \in participants : decision[p] # undecided => decision[p] = phase

SendRequest ==
  /\ coordState = waiting
  /\ coordState' = "request"
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, phase, forward>>

GetVote(p) ==
  /\ coordState = "request"
  /\ alive[p]
  /\ ~voted[p]
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ coordState' = "vote"
  /\ UNCHANGED <<vote, alive, decision, faulty, phase, forward>>

DetectFault(p) ==
  /\ coordState = "request"
  /\ ~alive[p]
  /\ coordState' = "vote"
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, phase, forward>>

MakeDecision ==
  /\ coordState \in {"request", "vote"}
  /\ \A p \in participants : voted[p]
  /\ phase' = IF \E p \in participants : vote[p] = no THEN abort ELSE commit
  /\ coordState' = "decide"
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, forward>>

Broadcast(p) ==
  /\ coordState = "decide"
  /\ alive[p]
  /\ forward' = [forward EXCEPT ![p] = [q \in participants |-> IF q = p THEN phase ELSE notsent]]
  /\ coordState' = "broadcast"
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, phase>>

PreDecideFromCoord(p) ==
  /\ coordState = "broadcast"
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forward[p][p] = notsent
  /\ forward' = [forward EXCEPT ![p][p] = phase]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordState, phase>>

PreDecideFromPeer(p, q) ==
  /\ q # p
  /\ alive[p]
  /\ decision[p] = undecided
  /\ alive[q]
  /\ forward[q][p] # notsent
  /\ forward[p][p] = notsent
  /\ forward' = [forward EXCEPT ![p][p] = forward[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordState, phase>>

Forward(p, q) ==
  /\ alive[p]
  /\ q # p
  /\ alive[q]
  /\ forward[p][p] # notsent
  /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordState, phase>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : q # p => forward[p][q] # notsent
  /\ forward[p][p] # notsent
  /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordState, phase, forward>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordState = "dead"
  /\ (\A q \in participants : coordState # "broadcast" => forward[q][p] = notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voted, coordState, phase, forward>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voted, coordState, phase, forward>>

DieCoordinator ==
  /\ coordState \in {"request", "vote"}
  /\ coordState' = "dead"
  /\ UNCHANGED <<vote, alive, decision, faulty, voted, phase, forward>>

CoordinatorProgress ==
  \/ SendRequest
  \/ \E p \in participants : GetVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants : Broadcast(p)
  \/ DieCoordinator

ParticipantProgress ==
  \/ \E p \in participants : PreDecideFromCoord(p)
  \/ \E p \in participants, q \in participants : PreDecideFromPeer(p, q)
  \/ \E p \in participants, q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortOnTimeout(p)

NextNB ==
  \/ CoordinatorProgress
  \/ ParticipantProgress
  \/ \E p \in participants : Die(p)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(CoordinatorProgress)
  /\ WF_vars(ParticipantProgress)

\* AC1: No two participants disagree on the decision.
Agreement ==
  \A p, q \in participants : decision[p] = undecided \/ decision[p] = decision[q]

\* AC2: A commit requires unanimity for yes.
CommitValidity == (\E p \in participants : decision[p] = commit) => \A q \in participants : vote[q] = yes

\* AC3: An abort must be backed by a no vote or a failure.
AbortValidity ==
  (\E p \in participants : decision[p] = abort) =>
    \/ \E q \in participants : vote[q] = no
    \/ \E q \in participants : faulty[q]
    \/ coordState = "dead"

\* AC4: Decisions are final once made.
Irreversibility == \A p \in participants : (decision[p] # undecided /\ alive[p]) => decision[p] = phase

\* AC5: Every non-faulty participant eventually decides (non-blocking termination).
DecideEventually == \A p \in participants : (alive[p] /\ ~faulty[p]) ~> (decision[p] # undecided)

====
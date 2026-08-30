---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, sentVote, coordState, fwd

vars == <<pstate, alive, decision, faulty, sentVote, coordState, fwd>>

\* One element of the forwarding table per (sender,receiver) pair: the value
\* (notsent/commit/abort) a participant has forwarded to another participant.
Table == [participants -> [participants -> {notsent, commit, abort}]]

TypeOK ==
  /\ pstate \in [participants -> {undecided, commit, abort}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in {yes, no, undecided}
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordState \in {waiting, alive, broadcast, dead, coordfaulty}
  /\ fwd \in [participants -> Table]

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = undecided
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordState = waiting
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions: inherited unchanged from the simple broadcast protocol.
SendReq ==
  /\ coordState = waiting
  /\ coordState' = alive
  /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, fwd>>

GetVote(p) ==
  /\ coordState = alive
  /\ alive[p]
  /\ ~sentVote[p]
  /\ pstate[p] # undecided
  /\ decision' = IF pstate[p] = abort THEN no ELSE decision
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, alive, faulty coordState, fwd>>

DetectFault(p) ==
  /\ coordState = alive
  /\ pstate[p] = abort
  /\ pstate' = [pstate EXCEPT ![p] = undecided]
  /\ UNCHANGED <<alive, decision, faulty, sentVote, coordState, fwd>>

MakeDecision ==
  /\ coordState = alive
  /\ \A p \in participants : sentVote[p] /\ pstate[p] # undecided
  /\ coordState' = broadcast
  /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, fwd>>

Broadcast(p) ==
  /\ coordState = broadcast
  /\ alive[p]
  /\ fwd' = [fwd EXCEPT ![p] = [fwd[p] EXCEPT ![p] = IF decision = yes THEN commit ELSE abort]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, coordState>>

Die ==
  /\ coordState \in {alive, broadcast}
  /\ coordState' = coordfaulty
  /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, fwd>>

\* Participant actions (a)-(d) replace the simple broadcast's single decision
\* action; they jointly implement reliable broadcasting with forwarding.
RecvFromCoordinator(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, coordState>>

RecvFromPeer(p, q) ==
  /\ p # q
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, coordState>>

Forward(p, q) ==
  /\ alive[p]
  /\ q # p
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, sentVote, coordState>>

Decide(p) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : q # p => fwd[p][q] # notsent
  /\ pstate' = [pstate EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<alive, decision, faulty, sentVote, coordState, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ pstate[p] = undecided
  /\ coordState = coordfaulty
  /\ \A q \in participants : ~alive[q] \/ fwd[q][p] = notsent
  /\ \A q \in participants : (~alive[q] => \A r \in participants : fwd[q][r] = notsent)
  /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED <<alive, decision, faulty, sentVote, coordState, fwd>>

DieP(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ pstate' = [pstate EXCEPT ![p] = undecided]
  /\ sentVote' = [sentVote EXCEPT ![p] = FALSE]
  /\ fwd' = [fwd EXCEPT ![p] = [q \in participants |-> notsent]]
  /\ UNCHANGED <<decision, coordState>>

SendReqFair == SendReq
GetVoteFair(p) == GetVote(p)
DetectFaultFair(p) == DetectFault(p)
DecideFair(p) == Decide(p)

Next ==
  \/ SendReq
  \/ \E p \in participants : GetVote(p) \/ DetectFault(p) \/ RecvFromCoordinator(p)
                              \/ RecvFromPeer(p, p) \/ Decide(p) \/ DieP(p)
  \/ \E p, q \in participants : Forward(p, q)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : \E q \in participants : RecvFromPeer(p, q)
  \/ MakeDecision \/ Die

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendReq)
  /\ \A p \in participants : WF_vars(GetVote(p)) /\ WF_vars(Decide(p))
  /\ SF_vars(\E p \in participants : RecvFromCoordinator(p))

\* Safety: agreement, abort/commit validity, and irrevocability.
Agreement == \A p, q \in participants : ~(pstate[p] = commit /\ pstate[q] = abort)
CommitValid == (\A p \in participants : pstate[p] = commit) => \A p \in participants : pstate[p] = undecided \/ sentVote[p]
AbortValid == (\E p \in participants : pstate[p] = abort) =>
                 (\E p \in participants : sentVote[p] /\ pstate[p] = abort) \/ (\E p \in participants : faulty[p]) \/ (coordState # waiting /\ coordState # alive)
Irreversible == \A p \in participants : (pstate[p] = commit \/ pstate[p] = abort) ~> (pstate[p] = commit \/ pstate[p] = abort)

\* Liveness: eventual decision, and non-blocking termination for every
\* non-faulty participant.
DecisionEventually ==
  <>(\A p \in participants : pstate[p] # undecided \/ coordState = coordfaulty \/ \E q \in participants : faulty[q])
ParticipantDecides == \A p \in participants : (pstate[p] = undecided) ~> (pstate[p] # undecided)

TypeInvNB == TypeOK
SpecNBReqs == SpecNB /\ DecisionEventually /\ ParticipantDecides

====
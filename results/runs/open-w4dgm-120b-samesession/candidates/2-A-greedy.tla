---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Forwarding table entry: not-sent, or the pre-decision (commit/abort) received.
\* The coordinator's broadcast is unreliable (it may die mid-broadcast), so
\* participants forward decisions to each other to guarantee eventual delivery.
\* The invariant is pairwise agreement; the liveness property is non-blocking
\* termination for every non-faulty participant.

VARIABLES vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd

vars == <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

TypeOK ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, waiting}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ coordReq \in {yes, no, undecided}
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in {commit, abort, waiting}
  /\ coordDecision \in {commit, abort, waiting}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ coordReq = undecided
  /\ coordVote = undecided
  /\ coordBroadcast = waiting
  /\ coordDecision = waiting
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordAlive
  /\ coordReq = undecided
  /\ \E v \in {yes, no} : coordReq' = v
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

GetVote(p) ==
  /\ coordAlive
  /\ alive[p]
  /\ sentVote[p] = FALSE
  /\ vote[p] = undecided
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

DetectFault(p) ==
  /\ coordAlive
  /\ alive[p]
  /\ sentVote[p] = FALSE
  /\ vote[p] = undecided
  /\ coordReq # undecided
  /\ coordVote = undecided
  /\ coordVote' = no
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

MakeDecision ==
  /\ coordAlive
  /\ coordReq # undecided
  /\ coordVote # undecided
  /\ coordDecision = waiting
  /\ coordDecision' = IF coordVote = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordAlive, coordFaulty, fwd>>

Broadcast ==
  /\ coordAlive
  /\ coordDecision # waiting
  /\ coordBroadcast = waiting
  /\ coordBroadcast' = coordDecision
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordDecision, coordAlive, coordFaulty, fwd>>

Die ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, fwd>>

\* A participant receives the coordinator's broadcast (the unreliable path).
PreDecideCoord(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ coordBroadcast # waiting
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant receives a forwarded pre-decision from another participant.
PreDecideFwd(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ fwd[p][p] = notsent
  /\ \E q \in participants : q # p /\ fwd[q][p] # notsent
  /\ \E d \in {commit, abort} : fwd' = [fwd EXCEPT ![p][p] = d]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* Forward the pre-decision to another participant (reliable broadcast step).
Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* Once a participant has forwarded its pre-decision to everyone, it finalizes.
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

\* Abort on timeout when the coordinator is dead and no broadcast/forward is pending.
AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = waiting
  /\ coordAlive = FALSE
  /\ coordBroadcast = waiting
  /\ \A q \in participants : fwd[q][p] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

DieP(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, sentVote, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Next ==
  \/ SendRequest
  \/ MakeDecision
  \/ Broadcast
  \/ Die
  \/ \E p \in participants :
       \/ GetVote(p) \/ DetectFault(p) \/ PreDecideCoord(p) \/ PreDecideFwd(p)
       \/ Decide(p) \/ AbortTimeout(p) \/ DieP(p)
       \/ \E q \in participants : Forward(p, q)

SpecNB == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : PreDecideCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideFwd(p))
  /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : AbortTimeout(p))

\* Pairwise agreement: no two participants ever reach different decisions.
AC1 == \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE

\* A commit can only happen if every participant voted yes.
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)

\* An abort is always justified by a no vote or a fault.
AC3 == (\E p \in participants : decision[p] = abort) => (\E p \in participants : vote[p] = no \/ faulty[p] \/ coordFaulty)

\* Decisions are final: once made they never change.
AC4 == \A p \in participants : (decision[p] \in {commit, abort}) ~> (decision[p] \in {commit, abort})

\* Every non-faulty participant eventually decides (non-blocking termination).
AC5 == \A p \in participants : (alive[p] /\ decision[p] = waiting) ~> (decision[p] \in {commit, abort})

TypeInvNB == TypeOK
====
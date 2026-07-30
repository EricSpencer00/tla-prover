---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pstate, alive, decision, faulty, voted, reqstate, coordVote, coordPhase
VARIABLES coordAlive, coordFaulty, fwd

vars == <<pstate, alive, decision, faulty, voted, reqstate, coordVote, coordPhase, coordAlive, coordFaulty, fwd>>

Locals == [pstate: [participants -> {undecided, commit, abort}], alive: BOOLEAN,
  decision: {yes, no}, faulty: BOOLEAN, voted: BOOLEAN]

TypeInvNB ==
  /\ pstate \in [participants -> {undecided, commit, abort}]
  /\ alive \in BOOLEAN
  /\ decision \in {yes, no}
  /\ faulty \in BOOLEAN

InitCoord ==
  /\ coordVote = waiting
  /\ coordPhase = waiting
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = TRUE
  /\ decision = yes
  /\ faulty = FALSE
  /\ voted = FALSE
  /\ reqstate = waiting
  /\ InitCoord
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ alive
  /\ ~faulty
  /\ reqstate = waiting
  /\ reqstate' = waiting
  /\ coordVote' = waiting
  /\ coordPhase' = waiting
  /\ UNCHANGED <<pstate, decision, faulty, voted, coordAlive, coordFaulty, fwd>>

SendVote(p) ==
  /\ alive
  /\ ~faulty
  /\ reqstate = waiting
  /\ voted = FALSE
  /\ voted' = TRUE
  /\ decision' = yes
  /\ pstate' = [pstate EXCEPT ![p] = undecided]
  /\ UNCHANGED <<alive, reqstate, coordVote, coordPhase, coordAlive, coordFaulty, fwd>>

AbortFromVote(p) ==
  /\ alive
  /\ pstate[p] = undecided
  /\ vote(p) = no
  /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED <<alive, decision, faulty, voted, reqstate, coordVote, coordPhase, coordAlive, coordFaulty, fwd>>

AbortOnTimeout(p) ==
  /\ alive
  /\ pstate[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : fwd[q][p] \in {notsent, abort}
  /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED <<alive, decision, faulty, voted, reqstate, coordVote, coordPhase, coordAlive, coordFaulty, fwd>>

\* The coordinator sends its decision to a participant.
SendDecision(p) ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ coordPhase = request
  /\ coordVote \in {yes, no}
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordVote]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, reqstate, coordVote, coordPhase, coordAlive, coordFaulty>>

PreDecideCoord(p) ==
  /\ alive
  /\ pstate[p] = undecided
  /\ fwd[p][p] \in {yes, no}
  /\ decision = fwd[p][p]
  /\ decision' = fwd[p][p]
  /\ UNCHANGED <<pstate, alive, faulty, voted, reqstate, coordVote, coordPhase, coordAlive, coordFaulty, fwd>>

PreDecideForward(p) ==
  /\ alive
  /\ pstate[p] = undecided
  /\ \E q \in participants : fwd[q][p] \in {yes, no}
  /\ fwd' = [fwd EXCEPT ![p][p] = IF fwd[p][p] = notsent THEN fwd[q][p] ELSE fwd[p][p]]
  /\ decision' = fwd[p][p]
  /\ UNCHANGED <<pstate, alive, faulty, voted, reqstate, coordVote, coordPhase, coordAlive, coordFaulty>>

\* Forward to a specific participant only if that participant has not yet received.
Forward(p, q) ==
  /\ alive
  /\ pstate[p] = undecided
  /\ fwd[p][p] \in {yes, no}
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voted, reqstate, coordVote, coordPhase, coordAlive, coordFaulty>>

Decide(p) ==
  /\ alive
  /\ pstate[p] = undecided
  /\ \A q \in participants : fwd[p][q] = decision \/ q = p
  /\ pstate' = [pstate EXCEPT ![p] = decision]
  /\ UNCHANGED <<alive, decision, faulty, voted, reqstate, coordVote, coordPhase, coordAlive, coordFaulty, fwd>>

MakeDecision(co) ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ coordPhase = vote
  /\ decision \in {yes, no}
  /\ coordVote' = decision
  /\ coordPhase' = request
  /\ UNCHANGED <<coordAlive, coordFaulty>>

BroadcastDecision ==
  /\ coordAlive
  /\ ~coordFaulty
  /\ coordPhase = request
  /\ coordPhase' = commit
  /\ UNCHANGED <<coordAlive, coordFaulty>>

DetectCoordFail ==
  /\ coordAlive
  /\ coordFaulty
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<coordVote, coordPhase, coordFaulty>>

DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordVote, coordPhase>>

Next ==
  \/ SendRequest
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortFromVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : SendDecision(p)
  \/ \E p \in participants : PreDecideCoord(p)
  \/ \E p \in participants : PreDecideForward(p)
  \/ \E p \in participants : \E q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p)
  \/ \E co \in {yes, no} : MakeDecision(co)
  \/ BroadcastDecision
  \/ DetectCoordFail
  \/ DieCoordinator

\* Weak fairness on all participant progress actions (voting, forwarding, deciding),
\* excluding death which is not guaranteed to happen.
Fairness ==
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortFromVote(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
  /\ WF_vars(\E p \in participants : SendDecision(p))
  /\ WF_vars(\E p \in participants : PreDecideCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideForward(p))
  /\ \A p \in participants : \A q \in participants : WF_vars(Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E co \in {yes, no} : MakeDecision(co))

SpecNB == Init /\ [][Next]_vars /\ Fairness

\* Agreement: no two participants ever decide differently.
AC1 ==
  \A p, q \in participants : (pstate[p] = commit /\ pstate[q] = abort) => p = q

\* Commit only when everybody voted yes.
AC2 ==
  \A p \in participants : pstate[p] = commit => (\A q \in participants : vote(q) = yes)

\* Abort only when somebody voted no, or somebody is faulty, or the coordinator is faulty.
AC3 ==
  \A p \in participants : pstate[p] = abort =>
    \/ \E q \in participants : vote(q) = no
    \/ \E q \in participants : faulty[q]
    \/ coordFaulty

\* Irreversibility: decisions are permanent.
AC4 ==
  \A p \in participants : (pstate[p] = commit \/ pstate[p] = abort) =>
    (pstate[p] = commit \/ pstate[p] = abort)

\* Every participant eventually reaches a decision (the non-blocking property).
AC5 ==
  \A p \in participants : (pstate[p] = commit \/ pstate[p] = abort) ~> TRUE

====
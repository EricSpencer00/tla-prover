---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, coordAlive, coordFaulty, forwarded, cstate

vars == <<vote, alive, decision, faulty, coordAlive, coordFaulty, forwarded, cstate>>

\* `cstate` is the coordinator: req/waiting, vote/i, broadcast/i, decision/i
\* `forwarded` is the per-participant forwarding table of the reliable broadcast

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forwarded \in [participants -> [participants -> {commit, abort, notsent}]]
  /\ cstate \in
       {[req |-> {waiting, commit, abort}] \cup
        [vote |-> {yes, no, undecided}] \cup
        [broadcast |-> {yes, no, notsent}] \cup
        [decision |-> {commit, abort, waiting}] \cup
        [alive |-> BOOLEAN] \cup
        [faulty |-> BOOLEAN]}

InitNB ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]
  /\ cstate = [req |-> waiting, vote |-> undecided,
               broadcast |-> notsent, decision |-> waiting,
               alive |-> TRUE, faulty |-> FALSE]

SendReq ==
  /\ coordAlive
  /\ cstate.req = waiting
  /\ cstate' = [cstate EXCEPT !.req = commit]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordAlive, coordFaulty, forwarded>>

GetVote(p) ==
  /\ coordAlive
  /\ cstate.req # waiting
  /\ vote[p] = undecided
  /\ \E x \in {yes, no} : vote' = [vote EXCEPT ![p] = x]
  /\ UNCHANGED <<alive, decision, faulty, coordAlive, coordFaulty, forwarded, cstate>>

DetectFault(p) ==
  /\ coordAlive
  /\ vote[p] = undecided
  /\ cstate.broadcast = notsent
  /\ cstate' = [cstate EXCEPT !.broadcast = no]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordAlive, coordFaulty, forwarded>>

MakeDecision(c) ==
  /\ coordAlive
  /\ cstate.broadcast = yes
  /\ cstate' = [cstate EXCEPT !.decision = c]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordAlive, coordFaulty, forwarded>>

\* Even after the coordinator dies, participants keep forwarding, so the broadcast
\* is never cut off by a coordinator failure.
Broadcast ==
  /\ coordAlive
  /\ cstate.decision # waiting
  /\ cstate.broadcast = notsent
  /\ cstate' = [cstate EXCEPT !.broadcast = cstate.decision]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordAlive, coordFaulty, forwarded>>

DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ cstate' = [cstate EXCEPT !.alive = FALSE]
  /\ UNCHANGED <<vote, alive, decision, faulty, forwarded, coordFaulty>>

SendVote(p) ==
  /\ alive[p]
  /\ ~faulty[p]
  /\ vote[p] # undecided
  /\ ~ coordFaulty
  /\ cstate.req # waiting
  /\ cstate.vote = undecided
  /\ cstate' = [cstate EXCEPT !.vote = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordAlive, coordFaulty, forwarded>>

AbortOnCoordVote(p) ==
  /\ alive[p]
  /\ ~faulty[p]
  /\ cstate.vote = no
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, coordAlive, coordFaulty, forwarded, cstate>>

\* New: a participant may pre-decision from a coordinator broadcast.
PreDecideCoord(p) ==
  /\ alive[p]
  /\ forwarded[p][p] = notsent
  /\ cstate.broadcast # notsent
  /\ forwarded' = [forwarded EXCEPT ![p][p] = cstate.broadcast]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordAlive, coordFaulty, cstate>>

\* New: a participant may pre-decision from another participant's forward.
PreDecideForward(p) ==
  /\ alive[p]
  /\ forwarded[p][p] = notsent
  /\ \E q \in participants :
       forwarded[q][p] # notsent /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordAlive, coordFaulty, cstate>>

\* New: a participant forwards its pre-decision to each other participant.
Forward(p, q) ==
  /\ alive[p]
  /\ forwarded[p][p] # notsent
  /\ forwarded[p][q] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordAlive, coordFaulty, cstate>>

\* New: a participant decides only once it has forwarded to everyone else.
Decide(p) ==
  /\ alive[p]
  /\ forwarded[p][p] # notsent
  /\ \A q \in participants : forwarded[p][q] # notsent
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = forwarded[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, coordAlive, coordFaulty, forwarded, cstate>>

\* Aborts even if the coordinator died, as long as some decision still exists.
AbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ ~(\E q \in participants : alive[q] /\ cstate.broadcast # notsent)
  /\ ~(\E q \in participants : ~alive[q] /\ \E r \in participants : forwarded[q][r] # notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, coordAlive, coordFaulty, forwarded, cstate>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, coordAlive, coordFaulty, forwarded, cstate>>

\* Once every participant is dead or faulty, the system quiesces and stops.
Quiesce ==
  /\ ~coordAlive
  /\ \A p \in participants : ~alive[p]
  /\ UNCHANGED vars

NextNB ==
  \/ Quiesce
  \/ SendReq
  \/ DieCoordinator
  \/ Broadcast
  \/ \E p \in participants : GetVote(p) \/ DetectFault(p) \/ SendVote(p) \/ AbortOnCoordVote(p)
  \/ \E p \in participants : PreDecideCoord(p) \/ PreDecideForward(p) \/ Decide(p) \/ AbortTimeout(p) \/ Die(p)
  \/ \E c \in {commit, abort} : MakeDecision(c)
  \/ \E p \in participants : \E q \in participants : Forward(p, q)

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(\E p \in participants : PreDecideCoord(p))
  /\ WF_vars(\E p \in participants : PreDecideForward(p))
  /\ WF_vars(\E p \in participants : \E q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnCoordVote(p))
  /\ WF_vars(\E p \in participants : AbortTimeout(p))

\* AC1 is an invariant (agreement); AC2/AC3 are abort/commit validity checks.
\* AC4 is irrevocability (once decided it never changes); AC5 is termination.
AC1 == ~\E p \in participants, q \in participants : decision[p] = commit /\ decision[q] = abort

AC2 == (\E p \in participants : decision[p] = commit) => (\A q \in participants : vote[q] = yes)

AC3 == (\E p \in participants : decision[p] = abort)
         => (\E q \in participants : vote[q] = no \/ faulty[q] \/ coordFaulty)

AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort)
         ~> (decision[p] = commit \/ decision[p] = abort)

AC5 == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~>
         (decision[p] = commit \/ decision[p] = abort)

====
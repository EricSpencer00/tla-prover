---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentvote, cphase, cvote, cbin, cstate, forwarded

vars == <<vote, alive, decision, faulty, sentvote, cphase, cvote, cbin, cstate, forwarded>>

\* Inherited coordinator logic: request, voting, broadcast, crash
\* Newest participant actions: pre-decide from coordinator or forwarding,
\* forward to another participant, decide only after forwarding to all.

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ sentvote \subseteq participants
  /\ cphase \in {waiting, commit, abort}
  /\ cvote \in {yes, no}
  /\ cbin \subseteq participants
  /\ cstate \in {alive, faulty}
  /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ sentvote = {}
  /\ cphase = waiting
  /\ cvote = yes
  /\ cbin = {}
  /\ cstate = alive
  /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ cstate = alive
  /\ cphase = waiting
  /\ cphase' = waiting
  /\ cbin' = {}
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, cvote, cstate, forwarded>>

GetVote(p) ==
  /\ cstate = alive
  /\ vote[p] = undecided
  /\ alive[p]
  /\ sentvote' = sentvote \cup {p}
  /\ UNCHANGED <<vote, alive, decision, faulty, cphase, cvote, cbin, cstate, forwarded>>

DetectFault == ~/\(\E p \in participants : vote[p] = undecided /\ alive[p]/\) /\ cstate = alive /\ cstate' = faulty
                 /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, cphase, cvote, cbin, forwarded>>

MakeDecision ==
  /\ cstate = alive
  /\ cphase = waiting
  /\ cvote \in {yes, no}
  /\ cphase' = IF cvote = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, cvote, cbin, cstate, forwarded>>

BroadcastDecision ==
  /\ cstate = alive
  /\ cphase \in {commit, abort}
  /\ cbin' = cbin \cup participants
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, cphase, cvote, cstate, forwarded>>

Die(p) == alive[p] /\ alive' = [alive EXCEPT ![p] = FALSE] /\ UNCHANGED <<vote, decision, faulty, sentvote, cphase, cvote, cbin, cstate, forwarded>>

\* Participant receives a pre-decision from the coordinator.
PreDecideFromCoord(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ p \in cbin
  /\ decision' = [decision EXCEPT ![p] = cphase]
  /\ forwarded' = [forwarded EXCEPT ![p][p] = cphase]
  /\ UNCHANGED <<vote, alive, faulty, sentvote, cphase, cvote, cbin, cstate>>

\* Participant receives a pre-decision forwarded by another participant.
PreDecideFromForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \E q \in participants : p # q /\ decision[q] # undecided /\ forwarded[q][p] = decision[q]
  /\ decision' = [decision EXCEPT ![p] = decision[q]]
  /\ forwarded' = [forwarded EXCEPT ![p][p] = decision[q]]
  /\ UNCHANGED <<vote, alive, faulty, sentvote, cphase, cvote, cbin, cstate>>

\* Forward the pre-decision to one other participant.
Forward(p, q) ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ forwarded[p][q] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][q] = decision[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sentvote, cphase, cvote, cbin, cstate>>

\* Decide only after forwarding the pre-decision to all others.
DecideNB(p) ==
  /\ alive[p]
  /\ decision[p] # undecided
  /\ \A q \in participants : q # p => forwarded[p][q] = decision[p]
  /\ decision' = [decision EXCEPT ![p] = decision[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentvote, cphase, cvote, cbin, cstate, forwarded>>

\* Abort on timeout: coordinator dead, no broadcast, no forwarding from dead.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ cstate = faulty
  /\ cbin \cap participants = {}
  /\ \A q \in participants : q \notin faulty => \A r \in participants : forwarded[q][r] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentvote, cphase, cvote, cbin, cstate, forwarded>>

VoteStep == \E p \in participants : GetVote(p)
PreCoordStep == \E p \in participants : PreDecideFromCoord(p)
PreForwardStep == \E p \in participants : PreDecideFromForward(p)
DecideStep == \E p \in participants : DecideNB(p)
AbortStep == \E p \in participants : AbortOnTimeout(p)
ForwardStep == \E p, q \in participants : Forward(p, q)

NextNB ==
  \/ SendRequest \/ DetectFault \/ MakeDecision \/ BroadcastDecision
  \/ VoteStep \/ PreCoordStep \/ PreForwardStep \/ DecideStep \/ AbortStep
  \/ ForwardStep
  \/ \E p \in participants : Die(p)

\* Weak fairness on participant progress (including forwarding and pre-decision),
\* plus coordinator progress, excluding the death transition.
SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(VoteStep)
  /\ WF_vars(PreCoordStep)
  /\ WF_vars(PreForwardStep)
  /\ WF_vars(DecideStep \/ AbortStep)
  /\ SF_vars(DecideStep \/ AbortStep)
  /\ WF_vars(ForwardStep)
  /\ SF_vars(SendRequest \/ DetectFault \/ MakeDecision \/ BroadcastDecision)

\* Safety: no two participants reach different decisions.
AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)

\* Safety: a commit requires all yes-votes.
AC2 == (commit \in {decision[p] : p \in participants}) => (\A p \in participants : vote[p] = yes)

\* Safety: an abort requires a no-vote or a faulty actor.
AC3Inv == (abort \in {decision[p] : p \in participants}) =>
            \/ (\E p \in participants : vote[p] = no)
            \/ faulty # {}
            \/ cstate = faulty

\* Safety: decisions are irreversible.
AC4 == \A p \in participants : (decision[p] # undecided) ~> (decision[p] # undecided)

\* Liveness: eventual resolution (all decided, or some fault).
AC3Live == <>(\E p \in participants : decision[p] # undecided) \/ faulty # {} \/ cstate = faulty

\* Liveness: every non-faulty participant eventually reaches a decision
\* (non-blocking termination of the whole protocol).
AC5 == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====
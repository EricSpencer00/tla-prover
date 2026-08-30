---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Non-blocking two-phase commit: a participant must forward its pre-decision
\* to every other participant before it may finalize locally.  Forwarding is
\* what guarantees termination when the coordinator crashes mid-broadcast.
VARIABLES pstate, alive, pdecision, faulty, voted, forwarded, coord

Vars == << pstate, alive, pdecision, faulty, voted, forwarded, coord >>

TypeOK ==
  /\ pstate \in [participants -> {undecided, commit, abort}]
  /\ alive \in [participants -> BOOLEAN]
  /\ pdecision \in {yes, no, undecided}
  /\ faulty \in BOOLEAN
  /\ voted \in [participants -> BOOLEAN]
  /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]
  /\ coord \in [state |-> waiting, vote |-> undecided, broadcast |-> {}, decision |-> undecided, alive |-> TRUE, faulty |-> FALSE]

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ pdecision = undecided
  /\ faulty = FALSE
  /\ voted = [p \in participants |-> FALSE]
  /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]
  /\ coord = [state |-> waiting, vote |-> undecided, broadcast |-> {}, decision |-> undecided, alive |-> TRUE, faulty |-> FALSE]

SendRequest ==
  /\ coord.state = waiting
  /\ coord.vote = undecided
  /\ coord.alive
  /\ coord.state' = "collecting"
  /\ coord.broadcast' = {}
  /\ UNCHANGED << pstate, alive, pdecision, faulty, voted, forwarded, coord >>

Vote(p) ==
  /\ coord.state = "collecting"
  /\ alive[p]
  /\ ~voted[p]
  /\ \E v \in {yes, no} : coord.vote' = IF coord.vote = undecided THEN v ELSE coord.vote
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED << pstate, alive, pdecision, faulty, forwarded, coord >>

DetectFault ==
  /\ coord.alive
  /\ \E p \in participants : ~alive[p]
  /\ coord.faulty' = TRUE
  /\ coord.alive' = FALSE
  /\ UNCHANGED << pstate, alive, pdecision, faulty, voted, forwarded, coord >>

MakeDecision ==
  /\ coord.state = "collecting"
  /\ coord.vote # undecided
  /\ coord.decision' = IF coord.vote = yes THEN commit ELSE abort
  /\ coord.state' = "decided"
  /\ UNCHANGED << pstate, alive, pdecision, faulty, voted, forwarded, coord >>

Broadcast(p) ==
  /\ coord.alive
  /\ coord.state = "decided"
  /\ coord.broadcast' = coord.broadcast \cup {p}
  /\ UNCHANGED << pstate, alive, pdecision, faulty, voted, forwarded, coord >>

Die ==
  /\ coord.alive
  /\ coord.state = "decided"
  /\ coord.alive' = FALSE
  /\ coord.faulty' = TRUE
  /\ UNCHANGED << pstate, alive, pdecision, faulty, voted, forwarded, coord >>

\* A pre-decision arrives via coordinator broadcast.
PreDecideCoord(p) ==
  /\ alive[p]
  /\ forwarded[p][p] = notsent
  /\ p \notin coord.broadcast
  /\ pdecision # undecided
  /\ forwarded' = [forwarded EXCEPT ![p][p] = pdecision]
  /\ UNCHANGED << pstate, alive, pdecision, faulty, voted, coord >>

\* A pre-decision arrives via peer forwarding.
PreDecideFwd(p) ==
  /\ alive[p]
  /\ forwarded[p][p] = notsent
  /\ \E q \in participants : q # p /\ forwarded[q][p] # notsent
  /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[CHOOSE q \in participants : q # p /\ forwarded[q][p] # notsent][p]]
  /\ UNCHANGED << pstate, alive, pdecision, faulty, voted, coord >>

Forward(p, q) ==
  /\ alive[p]
  /\ p # q
  /\ forwarded[p][p] # notsent
  /\ forwarded[p][q] = notsent
  /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
  /\ UNCHANGED << pstate, alive, pdecision, faulty, voted, coord >>

Decide(p) ==
  /\ alive[p]
  /\ pstate[p] = undecided
  /\ forwarded[p][p] # notsent
  /\ \A q \in participants : q # p => forwarded[p][q] = forwarded[p][p]
  /\ pstate' = [pstate EXCEPT ![p] = forwarded[p][p]]
  /\ UNCHANGED << alive, pdecision, faulty, voted, forwarded, coord >>

AbortOnTimeout ==
  /\ coord.faulty
  /\ \A p \in participants : alive[p] => pstate[p] = undecided
  /\ \A p \in participants : ~alive[p] => pstate[p] = undecided
  /\ \A q \in participants : ~alive[q] => \A p \in participants : alive[p] => forwarded[q][p] = notsent
  /\ \E p \in participants : alive[p] /\ pstate' = [pstate EXCEPT ![p] = abort]
  /\ UNCHANGED << alive, pdecision, faulty, voted, forwarded, coord >>

Next ==
  \/ SendRequest
  \/ \E p \in participants : Vote(p)
  \/ DetectFault
  \/ MakeDecision
  \/ \E p \in participants : Broadcast(p)
  \/ Die
  \/ AbortOnTimeout
  \/ \E p \in participants : PreDecideCoord(p)
  \/ \E p \in participants : PreDecideFwd(p)
  \/ \E p, q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p)

SpecNB == Init /\ [][Next]_Vars
  /\ WF_Vars(\E p \in participants : PreDecideCoord(p))
  /\ WF_Vars(\E p \in participants : PreDecideFwd(p))
  /\ WF_Vars(\E p \in participants : \E q \in participants : Forward(p, q))
  /\ WF_Vars(\E p \in participants : Decide(p))

\* Safety: the action set never lets two participants commit and abort.
TypeInvNB == (\A p, q \in participants : (pstate[p] = commit /\ pstate[q] = abort) => FALSE)
  /\ (\A p \in participants : pstate[p] = commit => pdecision = yes)
  /\ (\A p \in participants : pstate[p] = abort => (pdecision = no \/ faulty))

\* Liveness: aborts are triggered even when the coordinator silently dies.
AC3Live == <>(\A p \in participants : pstate[p] # undecided \/ faulty)

\* Progress is guaranteed by the forwarding-before-finalizing rule.
AC5 == \A p \in participants : (pstate[p] = undecided /\ ~faulty) ~> (pstate[p] # undecided)

====
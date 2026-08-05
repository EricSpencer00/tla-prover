---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteSent, coordState, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd

vars == <<vote, alive, decision, faulty, voteSent, coordState, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordState \in {waiting, notsent, commit, abort}
  /\ coordReq \in {yes, no, undecided}
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in [participants -> {yes, no, notsent}]
  /\ coordDecision \in {yes, no, notsent}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordState = waiting
  /\ coordReq = undecided
  /\ coordVote = undecided
  /\ coordBroadcast = [p \in participants |-> notsent]
  /\ coordDecision = notsent
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordState = waiting
  /\ coordAlive
  /\ coordState' = notsent
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

GetVote(p) ==
  /\ coordState = notsent
  /\ alive[p]
  /\ ~voteSent[p]
  /\ vote[p] # undecided
  /\ coordVote' = vote[p]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordState, coordReq, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

DetectFault ==
  /\ coordState = notsent
  /\ coordAlive
  /\ \E p \in participants : voteSent[p] /\ vote[p] = no
  /\ coordState' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

MakeDecision ==
  /\ coordState = notsent
  /\ coordAlive
  /\ \A p \in participants : voteSent[p] /\ vote[p] = yes
  /\ coordState' = commit
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Broadcast ==
  /\ coordState \in {commit, abort}
  /\ coordAlive
  /\ coordDecision' = coordState
  /\ coordBroadcast' = [p \in participants |-> coordState]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordState, coordReq, coordVote, coordAlive, coordFaulty, fwd>>

DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordState, coordReq, coordVote, coordBroadcast, coordDecision, fwd>>

SendVote(p) ==
  /\ coordState = waiting
  /\ alive[p]
  /\ vote[p] = undecided
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, coordState, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordState, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : coordBroadcast[q] = notsent
  /\ \A q \in participants : ~(\A r \in participants : ~faulty[r] /\ fwd[r][q] # notsent)
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordState, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

PreDecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ coordBroadcast[p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordState, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PreDecideFromForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ \E q \in participants : fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = fwd[CHOOSE q \in participants : fwd[q][p] # notsent][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordState, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordState, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordState, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voteSent, coordState, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Next ==
  \/ SendRequest
  \/ DetectFault
  \/ MakeDecision
  \/ Broadcast
  \/ DieCoordinator
  \/ \E p \in participants : GetVote(p)
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : PreDecideFromCoordinator(p)
  \/ \E p \in participants : PreDecideFromForward(p)
  \/ \E p \in participants, q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : Die(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnVote(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
  /\ WF_vars(\E p \in participants : PreDecideFromCoordinator(p))
  /\ WF_vars(\E p \in participants : PreDecideFromForward(p))
  /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
  /\ WF_vars(\E p \in participants : Decide(p))
  /\ WF_vars(\E p \in participants : Die(p))

AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)
AC2 == (\E p \in participants : decision[p] = commit) => (\A q \in participants : vote[q] = yes)
AC3 == (\E p \in participants : decision[p] = abort) => (\E q \in participants : vote[q] = no \/ faulty[q] \/ coordFaulty)
AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

AC3Liveness == <>(\A p \in participants : decision[p] # undecided \/ \E p \in participants : faulty[p] \/ coordFaulty)
AC5 == \A p \in participants : (decision[p] = undecided) ~> (decision[p] # undecided)

====
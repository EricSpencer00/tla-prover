---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd

vars == <<vote, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

TypeInvNB ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordReq \in {waiting, yes, no}
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in [participants -> {commit, abort, undecided}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordReq = waiting
  /\ coordVote = undecided
  /\ coordBroadcast = [p \in participants |-> undecided]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordAlive
  /\ coordReq = waiting
  /\ coordReq' = yes
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

GetVote(p) ==
  /\ coordAlive
  /\ coordReq # waiting
  /\ alive[p]
  /\ ~voteSent[p]
  /\ vote[p] # undecided
  /\ coordVote' = IF coordVote = undecided THEN vote[p] ELSE coordVote
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, coordReq, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

DetectFault(p) ==
  /\ coordAlive
  /\ coordReq # waiting
  /\ alive[p]
  /\ vote[p] = undecided
  /\ coordVote' = no
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

MakeDecision ==
  /\ coordAlive
  /\ coordReq # waiting
  /\ coordVote # undecided
  /\ coordDecision = undecided
  /\ coordDecision' = coordVote
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordAlive, coordFaulty, fwd>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordBroadcast[p] = undecided
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq, coordVote, coordDecision, coordAlive, coordFaulty, fwd>>

DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, fwd>>

SendVote(p) ==
  /\ alive[p]
  /\ vote[p] = undecided
  /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ vote[p] = no
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

PreDecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordBroadcast[p] # undecided
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PreDecideFromForward(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ \E q \in participants : fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = CHOOSE v \in {commit, abort} : \E q \in participants : fwd[q][p] = v]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : coordBroadcast[q] = undecided
  /\ \A q \in participants : \A r \in participants : (faulty[q] /\ fwd[q][r] # notsent) => r = p
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

NextNB ==
  \/ SendRequest
  \/ MakeDecision
  \/ Broadcast('a')
  \/ DieCoordinator
  \/ \E p \in participants :
       \/ GetVote(p) \/ DetectFault(p) \/ SendVote(p) \/ AbortOnVote(p)
       \/ PreDecideFromCoordinator(p) \/ PreDecideFromForward(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
       \/ \E q \in participants : Forward(p, q)

SpecNB == InitNB /\ [][NextNB]_vars
  /\ WF_vars(SendRequest) /\ WF_vars(MakeDecision) /\ WF_vars(Decide('a')) /\ WF_vars(AbortOnTimeout('a'))

AC1 == \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)
AC2 == (\E p \in participants : decision[p] = commit) => (\A p \in participants : vote[p] = yes)
AC3 == (\E p \in participants : decision[p] = abort) => (\E p \in participants : vote[p] = no \/ faulty[p] \/ coordFaulty)
AC4 == \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> decision[p]

AC3Liveness == <>(\A p \in participants : decision[p] # undecided \/ \E p \in participants : faulty[p] \/ coordFaulty)
AC5 == \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

====
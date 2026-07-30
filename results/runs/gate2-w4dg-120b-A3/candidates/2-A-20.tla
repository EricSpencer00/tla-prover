---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voteSent, coordReq, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty,
          fwd

vars == <<vote, alive, decision, faulty, voteSent, coordReq, coordVote,
          coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Types ==
  /\ vote \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordReq \in BOOLEAN
  /\ coordVote \in {yes, no, undecided}
  /\ coordBroadcast \in [participants -> {notsent, commit, abort}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordReq = FALSE
  /\ coordVote = undecided
  /\ coordBroadcast = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordAlive
  /\ ~coordReq
  /\ coordReq' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

GetVote(p, v) ==
  /\ coordAlive
  /\ coordReq
  /\ alive[p]
  /\ ~voteSent[p]
  /\ vote[p] = undecided
  /\ vote' = [vote EXCEPT ![p] = v]
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, decision, faulty, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

CoordDetectFault ==
  /\ coordAlive
  /\ coordVote = undecided
  /\ coordReq
  /\ coordVote' = no
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

MakeDecision(v) ==
  /\ coordAlive
  /\ coordVote' = v
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordVote # undecided
  /\ coordVote' = undecided
  /\ coordDecision' = decision
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = decision]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordAlive, coordFaulty, fwd>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroadcast, coordDecision, fwd>>

PreDecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ coordBroadcast[p] # notsent
  /\ fwd[p][p] = notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

PreDecideFromForward(p, q) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] = notsent
  /\ q # p
  /\ fwd[q][p] # notsent
  /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Forward(p, q) ==
  /\ alive[p]
  /\ p # q
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, voteSent, coordReq,
                coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

Decide(p) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] # notsent
  /\ decision[p] = undecided
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq,
                coordVote, coordBroadcast, coordDecision,
                coordAlive, coordFaulty, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : coordBroadcast[q] = notsent
  /\ \A q \in participants : \A r \in participants : fwd[q][r] # notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, voteSent, coordReq,
                coordVote, coordBroadcast, coordDecision,
                coordAlive, coordFaulty, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, voteSent, coordReq, coordVote,
                coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

CoordinatorProgress ==
  \/ CoordDetectFault \/ CoordDie

ParticipantProgress ==
  \E p \in participants :
    \/ \E v \in {yes, no} : GetVote(p, v)
    \/ \E q \in participants : Forward(p, q)
    \/ Decide(p) \/ Die(p) \/ AbortOnTimeout(p)
    \/ PreDecideFromCoordinator(p)
    \/ \E q \in participants : PreDecideFromForward(p, q)

Next ==
  \/ SendRequest \/ CoordinatorProgress
  \/ \E p \in participants : Broadcast(p)
  \/ \E p \in participants, v \in {yes, no} : GetVote(p, v)
  \/ \E p \in participants : PreDecideFromCoordinator(p)
  \/ \E p \in participants, q \in participants : PreDecideFromForward(p, q)
  \/ \E p, q \in participants : Forward(p, q)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : Die(p)

SpecNB == Init /\ [][Next]_vars
          /\ WF_vars(CoordinatorProgress)
          /\ WF_vars(ParticipantProgress)

TypeInvNB == Types

NoTwoDecideDifferently ==
  \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)

CommitValid == commit \in {decision[p] : p \in participants} => \A p \in participants : vote[p] = yes

AbortValid ==
  abort \in {decision[p] : p \in participants} =>
    \/ \E p \in participants : vote[p] = no
    \/ \E p \in participants : faulty[p]
    \/ coordFaulty

Irreversible ==
  \A p \in participants : (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

DecideEventually ==
  \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

DecideOrFault ==
  \A p \in participants : (alive[p] /\ decision[p] = undecided) ~> (decision[p] # undecided \/ coordFaulty \/ faulty[p])

====
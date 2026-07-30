---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordFaulty, coordDecision, coordBroadcast,
         vote, alive, decision, faulty, voted, fwd

vars == <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
          vote, alive, decision, faulty, voted, fwd>>

TypeInvNB ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordBroadcast \in [participants -> {waiting, yes, no}]
  /\ vote \in [participants -> {no, undecided, yes}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voted \in [participants -> BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = undecided
  /\ coordBroadcast = [p \in participants |-> waiting]
  /\ vote = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voted = [p \in participants |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
  /\ coordAlive /\ ~coordFaulty
  /\ coordDecision = undecided
  /\ coordBroadcast' = [p \in participants |-> waiting]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                vote, alive, decision, faulty, voted, fwd>>

GetVote(p) ==
  /\ coordAlive /\ ~coordFaulty
  /\ coordDecision = undecided
  /\ vote[p] \in {yes, no}
  /\ coordBroadcast[p] = waiting
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                vote, alive, decision, faulty, voted, fwd>>

DetectFault(p) ==
  /\ coordAlive /\ ~coordFaulty
  /\ ~voted[p]
  /\ vote' = [vote EXCEPT ![p] = no]
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                coordBroadcast, alive, decision, faulty, fwd>>

MakeDecision ==
  /\ coordAlive /\ ~coordFaulty
  /\ coordDecision = undecided
  /\ \A p \in participants : coordBroadcast[p] # waiting
  /\ coordDecision' = IF \A p \in participants : coordBroadcast[p] = yes
                       THEN commit ELSE abort
  /\ UNCHANGED <<coordAlive, coordFaulty, coordBroadcast,
                vote, alive, decision, faulty, voted, fwd>>

BroadcastDecision ==
  /\ coordAlive /\ ~coordFaulty
  /\ coordDecision # undecided
  /\ coordBroadcast' = [p \in participants |-> coordDecision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                vote, alive, decision, faulty, voted, fwd>>

DieCoordinator ==
  /\ coordAlive /\ ~coordFaulty
  /\ coordFaulty' = TRUE
  /\ coordAlive' = FALSE
  /\ UNCHANGED <<coordDecision, coordBroadcast,
                vote, alive, decision, faulty, voted, fwd>>

SendVote(p) ==
  /\ alive[p]
  /\ ~voted[p]
  /\ vote' = [vote EXCEPT ![p] = IF \E q \in participants : coordBroadcast[q] = no
                                   THEN no ELSE yes]
  /\ voted' = [voted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                alive, decision, faulty, fwd>>

AbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                vote, alive, faulty, voted, fwd>>

AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : coordBroadcast[q] # waiting
  /\ \A q \in participants : faulty[q] => decision[q] = undecided
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                vote, alive, faulty, voted, fwd>>

PreDecideCoord(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ coordBroadcast[p] # waiting
  /\ fwd' = [fwd EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                vote, alive, decision, faulty, voted>>

PreDecideFwd(p) ==
  /\ alive[p]
  /\ fwd[p][p] = notsent
  /\ \E q \in participants :
        /\ fwd[q][p] # notsent
        /\ fwd' = [fwd EXCEPT ![p][p] = fwd[q][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                vote, alive, decision, faulty, voted>>

Forward(p, q) ==
  /\ alive[p]
  /\ fwd[p][p] # notsent
  /\ fwd[p][q] = notsent
  /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                vote, alive, decision, faulty, voted>>

Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ fwd[p][p] # notsent
  /\ \A q \in participants : fwd[p][q] = fwd[p][p]
  /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                vote, alive, faulty, voted, fwd>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordBroadcast,
                vote, decision, voted, fwd>>

Next ==
  \/ SendRequest \/ MakeDecision \/ BroadcastDecision \/ DieCoordinator
  \/ \E p \in participants :
       SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p)
         \/ PreDecideCoord(p) \/ PreDecideFwd(p) \/ Decide(p) \/ Die(p)
         \/ \E q \in participants : Forward(p, q)
  \/ \E p \in participants : GetVote(p) \/ DetectFault(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p) \/ PreDecideCoord(p)
                                 \/ PreDecideFwd(p) \/ Decide(p))
  /\ WF_vars(\E p \in participants : Forward(p, CHOOSE q \in participants : TRUE))

AC1 ==
  \A p, q \in participants :
    (decision[p] = commit /\ decision[q] = abort) => FALSE

AC2 ==
  \A p \in participants : (decision[p] = commit) => \A q \in participants : vote[q] = yes

AC3 ==
  \A p \in participants :
    (decision[p] = abort) =>
      \/ \E q \in participants : vote[q] = no
      \/ \E q \in participants : faulty[q]
      \/ coordFaulty

AC4 ==
  \A p \in participants :
    (decision[p] = commit) => (decision[p] = commit)
    /\ (decision[p] = abort) => (decision[p] = abort)

AllDecided == \A p \in participants : decision[p] # undecided

AC3Liveness ==
  <>(AllDecided \/ \E p \in participants : faulty[p] \/ coordFaulty)

AC5 ==
  \A p \in participants : (decision[p] # undecided) ~> (decision[p] # undecided)

====
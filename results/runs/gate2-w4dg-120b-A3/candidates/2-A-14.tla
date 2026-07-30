---- MODULE ACP_NB ----
EXTENDS Naturals

\* Non-Blocking Atomic Commitment Protocol (ACP-NB).
\* Extends the base simple broadcast protocol by adding a forwarding
\* table per participant; the participant must forward its pre-decision
\* to every other participant before finalizing locally, so a crashed
\* coordinator never permanently stalls a non-faulty participant.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pvote, palive, pdecision, pfaulty, pvoteSent
VARIABLES pforward, coordRequest, coordVote, coordBroadcast
VARIABLES coordDecision, coordAlive, coordFaulty

vars == << pvote, palive, pdecision, pfaulty, pvoteSent, pforward,
           coordRequest, coordVote, coordBroadcast,
           coordDecision, coordAlive, coordFaulty >>

Coordinator == "coordinator"

InitCoord == coordinatoreq /\ ~coordfails

InitCoord0 == coordinatoreq /\ coordfails
InitCoord1 == coordinatoreq /\ ~coordfails

\* participants is a constant set; the forwarding table is a function
\* from participants to the set {notsent, commit, abort}, tracking both
\* the participant's own pre-decision (at its own index) and the decisions
\* it has already forwarded to others.
InitForward == [p \in participants |-> [q \in participants |-> notsent]]

InitCoordVars ==
  /\ coordRequest = waiting
  /\ coordVote = none
  /\ coordBroadcast = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

Init ==
  /\ pvote = [p \in participants |-> none]
  /\ palive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ pvoteSent = [p \in participants |-> FALSE]
  /\ pforward = InitForward
  /\ InitCoordVars

\* Base coordinator actions (inherited, unchanged) from ACP-SB.
SendRequest ==
  /\ coordAlive
  /\ coordRequest = waiting
  /\ coordRequest' = "active"
  /\ UNCHANGED << coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty, pvote, palive, pdecision,
                 pfaulty, pvoteSent, pforward >>

ReceiveVote(p) ==
  /\ coordAlive
  /\ coordRequest = "active"
  /\ coordVote = none
  /\ pvote[p] = yes \/ pvote[p] = no
  /\ (coordVote' = pvote[p])
  /\ pvoteSent' = [pvoteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << coordRequest, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty, pvote, palive, pdecision,
                 pfaulty, pforward >>

Vote(p, v) ==
  /\ coordAlive
  /\ pvote[p] = none
  /\ pvote' = [pvote EXCEPT ![p] = v]
  /\ UNCHANGED << coordRequest, coordVote, coordBroadcast,
                 coordDecision, coordAlive, coordFaulty,
                 palive, pdecision, pfaulty, pvoteSent, pforward >>

DetectFault ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordVote # none
  /\ coordVote' = no
  /\ UNCHANGED << coordRequest, coordVote, coordBroadcast,
                 coordDecision, coordAlive, coordFaulty,
                 pvote, palive, pdecision, pfaulty, pvoteSent, pforward >>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordVote # none
  /\ coordDecision' = coordVote
  /\ UNCHANGED << coordRequest, coordVote, coordBroadcast,
                 coordAlive, coordFaulty,
                 pvote, palive, pdecision, pfaulty, pvoteSent, pforward >>

Broadcast(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordBroadcast[p] = notsent
  /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED << coordRequest, coordVote, coordDecision,
                 coordAlive, coordFaulty,
                 pvote, palive, pdecision, pfaulty, pvoteSent, pforward >>

DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << coordRequest, coordVote, coordBroadcast,
                 coordDecision, pvote, palive, pdecision,
                 pfaulty, pvoteSent, pforward >>

\* New participant actions (replacing the simple broadcast finalize):
\* pre-decision from coordinator broadcast, pre-decision from forwarding,
\* forwarding, finalize once all forwards are done, abort-on-timeout.
PreDecideFromCoordinator(p) ==
  /\ palive[p]
  /\ coordBroadcast[p] # notsent
  /\ pforward[p][p] = notsent
  /\ pforward' = [pforward EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty, pvoteSent,
                 coordRequest, coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty >>

PreDecideFromForward(p) ==
  /\ palive[p]
  /\ pforward[p][p] = notsent
  /\ \E q \in participants :
        /\ pforward[q][p] # notsent
        /\ pforward' = [pforward EXCEPT ![p][p] = pforward[q][p]]
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty, pvoteSent,
                 coordRequest, coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty >>

Forward(p, q) ==
  /\ palive[p]
  /\ pforward[p][p] # notsent
  /\ pforward[p][q] = notsent
  /\ pforward' = [pforward EXCEPT ![p][q] = pforward[p][p]]
  /\ UNCHANGED << pvote, palive, pdecision, pfaulty, pvoteSent,
                 coordRequest, coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty >>

Decide(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ \A q \in participants : pforward[p][q] # notsent
  /\ pdecision' = [pdecision EXCEPT ![p] = pforward[p][p]]
  /\ UNCHANGED << pvote, palive, pfaulty, pvoteSent,
                 coordRequest, coordVote, coordBroadcast,
                 coordDecision, coordAlive, coordFaulty, pforward >>

AbortOnTimeout(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : coordBroadcast[q] = notsent
  /\ \A q \in participants :
        \A r \in participants :
            ~ ( ~palive[r] /\ pforward[q][r] # notsent )
  /\ pdecision' = [pdecision EXCEPT ![p] = abort]
  /\ UNCHANGED << pvote, palive, pfaulty, pvoteSent,
                 coordRequest, coordVote, coordBroadcast,
                 coordDecision, coordAlive, coordFaulty, pforward >>

Die(p) ==
  /\ palive[p]
  /\ palive' = [palive EXCEPT ![p] = FALSE]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << pvote, pdecision, pvoteSent,
                 coordRequest, coordVote, coordBroadcast, coordDecision,
                 coordAlive, coordFaulty, pforward >>

Next ==
  \/ SendRequest \/ DetectFault \/ MakeDecision \/ DieCoordinator
  \/ \E p \in participants : ReceiveVote(p) \/ Vote(p, yes) \/ Vote(p, no)
  \/ \E p \in participants : Broadcast(p) \/ PreDecideFromCoordinator(p)
  \/ \E p \in participants : PreDecideFromForward(p)
  \/ \E p \in participants : Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
  \/ \E p, q \in participants : Forward(p, q)

SpecNB == Init /\ [][Next]_vars
          /\ WF_vars(\E p \in participants : PreDecideFromCoordinator(p))
          /\ WF_vars(\E p \in participants : PreDecideFromForward(p))
          /\ WF_vars(\E p, q \in participants : Forward(p, q))
          /\ WF_vars(\E p \in participants : Decide(p))
          /\ WF_vars(\E p \in participants : Vote(p, yes))
          /\ WF_vars(\E p \in participants : Vote(p, no))
          /\ WF_vars(\E p \in participants : AbortOnTimeout(p))

\* Safety: agreement, commit validity, abort validity, irrevocability.
TypeInvNB ==
  /\ pvote \in [participants -> {none, yes, no}]
  /\ pdecision \in [participants -> {undecided, commit, abort}]
  /\ pforward \in [participants -> [participants -> {notsent, commit, abort}]]

\* Liveness: progress to a decision, or a crash; guaranteed by the
\* forwarding-before-finalizing scheme, which the simple broadcast lacks.
DecideEventually ==
  <>( \A p \in participants : pdecision[p] # undecided \/ pfaulty[p] )
  \/ coordFaulty

DecideAll ==
  <>( \A p \in participants : pdecision[p] # undecided )
  \/ (\E p \in participants : pfaulty[p]) \/ coordFaulty

====
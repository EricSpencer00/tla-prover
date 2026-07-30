---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Extends the simple broadcast variant (ACP-SB) by adding a forwarding table
\* to each participant. The forwarding table records both what pre-decision the
\* participant has received (at its own index) and which participants it has
\* already forwarded that pre-decision to. Forwarding to every other participant
\* is required before the participant finalizes its own decision, which is
\* what gives the reliable broadcast (non-blocking) guarantee.
Messages == {commit, abort}

VARIABLES pstate, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forward

vars == <<pstate, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

AllForwarded(i) == \A j \in participants \ {i} : forward[i][j] # notsent

TypeInvNB ==
  /\ pstate \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, undecided}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ coordReq \in BOOLEAN
  /\ coordVote \in {yes, no, waiting}
  /\ coordBroadcast \in [participants -> {commit, abort, none}]
  /\ coordDecision \in {commit, abort, waiting}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ pstate = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ coordReq = FALSE
  /\ coordVote = waiting
  /\ coordBroadcast = [p \in participants |-> none]
  /\ coordDecision = waiting
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions are identical to the base simple broadcast variant (ACP-SB).
SendRequest ==
  /\ coordAlive
  /\ \A p \in participants : alive[p]
  /\ coordReq = FALSE
  /\ coordReq' = TRUE
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

GetVote(p) ==
  /\ coordAlive
  /\ coordReq
  /\ coordVote = waiting
  /\ alive[p]
  /\ ~voteSent[p]
  /\ \E b \in {yes, no} : pstate[p] = b /\ coordVote' = b
  /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, alive, decision, faulty, coordReq, coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

DetectCoordFault ==
  /\ coordAlive
  /\ coordDecision = waiting
  /\ \E p \in participants : ~alive[p]
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, forward>>

MakeDecision(b) ==
  /\ coordAlive
  /\ coordDecision = waiting
  /\ coordVote = b
  /\ coordDecision' = b
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordAlive, coordFaulty, forward>>

Broadcast ==
  /\ coordAlive
  /\ coordDecision # waiting
  /\ coordBroadcast' = [p \in participants |-> coordDecision]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordReq, coordVote, coordDecision, coordAlive, coordFaulty, forward>>

\* Participant actions. Two are inherited from ACP-SB: SendVote and AbortVote.
SendVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ pstate[p] = undecided
  /\ coordVote = waiting
  /\ coordReq
  /\ pstate' = [pstate EXCEPT ![p] = yes]
  /\ UNCHANGED <<alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

AbortVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ pstate[p] = undecided
  /\ coordVote = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

AbortOnCoordinatorTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ \A q \in participants : coordBroadcast[q] = none
  /\ \A da \in participants : faulty[da] => \A q \in participants : forward[da][q] = notsent
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

Die(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pstate, decision, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

\* New: receive a pre-decision broadcasted directly from the coordinator.
PreDecideFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forward[p][p] = notsent
  /\ coordBroadcast[p] # none
  /\ forward' = [forward EXCEPT ![p][p] = coordBroadcast[p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* New: receive a pre-decision forwarded by another alive participant.
PreDecideFromParticipant(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ forward[p][p] = notsent
  /\ \E q \in participants : q # p /\ alive[q] /\ forward[q][p] # notsent
  /\ forward' = [forward EXCEPT ![p][p] = CHOOSE m \in {commit, abort} : \E q \in participants : q # p /\ alive[q] /\ forward[q][p] = m]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* New: forward a received pre-decision to another participant that has not yet
\* received it.
ForwardDecision(p) ==
  /\ alive[p]
  /\ forward[p][p] # notsent
  /\ \E q \in participants : q # p /\ forward[p][q] = notsent
  /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
  /\ UNCHANGED <<pstate, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* New: finalize the decision once this participant has forwarded its pre-
\* decision to every other participant (the non-blocking guarantee).
Decide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ AllForwarded(p)
  /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
  /\ UNCHANGED <<pstate, alive, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>

Next ==
  \/ SendRequest \/ DetectCoordFault \/ Broadcast
  \/ \E p \in participants : SendVote(p) \/ AbortVote(p) \/ AbortOnCoordinatorTimeout(p) \/ Die(p) \/ PreDecideFromCoordinator(p) \/ PreDecideFromParticipant(p) \/ ForwardDecision(p) \/ Decide(p)
  \/ \E b \in {yes, no} : MakeDecision(b)

vars == <<pstate, alive, decision, faulty, voteSent, coordReq, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, forward>>
SpecNB == Init /\ [][Next]_vars

\* Safety: no two participants ever commit and abort at once, and abort/commit only
\* under a legitimate cause (a no vote, a faulty participant, or a faulty
\* coordinator). Irrevocability is also part of the safety set.
Agreement == \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE
CommitValidity == (\E p \in participants : decision[p] = commit) => (\A p \in participants : pstate[p] = yes)
AbortValidity == (\E p \in participants : decision[p] = abort) => (\E q \in participants : pstate[q] = no \/ faulty[q] \/ coordFaulty)
Irreversible == \A p \in participants : (decision[p] = undecided) ~> (decision[p] # undecided)
TypeInvNB == TypeInvNB

\* Liveness: the whole run resolves or a failure is exposed; every non-faulty
\* participant eventually decides (non-blocking, which relies on forwarding).
Resolution == <>(\A p \in participants : decision[p] # undecided \/ faulty[p] \/ coordFaulty)
NoBlock == <>(\A p \in participants : alive[p] ~> decision[p] # undecided)

Properties == {Agreement, CommitValidity, AbortValidity, Irreversible, Resolution, NoBlock}
====
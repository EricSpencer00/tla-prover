---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote, coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd

vars == <<vote, alive, decision, faulty, sentVote, coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Bump == IF coordDecision = commit THEN abort ELSE commit

TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ coordRequest \in BOOLEAN
    /\ coordVote \in [participants -> {yes, no, undecided}]
    /\ coordBroadcast \in [participants -> {commit, abort, waiting}]
    /\ coordDecision \in {commit, abort, waiting}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ coordRequest = FALSE
    /\ coordVote = [p \in participants |-> undecided]
    /\ coordBroadcast = [p \in participants |-> waiting]
    /\ coordDecision = waiting
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
    /\ coordAlive
    /\ ~coordRequest
    /\ coordRequest' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

GetVote(p) ==
    /\ coordRequest
    /\ alive[p]
    /\ sentVote[p] = FALSE
    /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, coordRequest, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

DetectFault ==
    /\ coordAlive
    /\ coordDecision = waiting
    /\ \E p \in participants:
        /\ alive[p]
        /\ coordVote[p] = no
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, sentVote, coordRequest, coordVote, coordBroadcast, coordAlive, coordFaulty, fwd>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = waiting
    /\ \A p \in participants: coordVote[p] = yes
    /\ coordDecision' = commit
    /\ UNCHANGED <<vote, alive, sentVote, coordRequest, coordVote, coordBroadcast, coordAlive, coordFaulty, fwd>>

BroadcastDecision ==
    /\ coordAlive
    /\ coordDecision # waiting
    /\ \E p \in participants:
        /\ coordBroadcast[p] = waiting
        /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordRequest, coordVote, coordDecision, coordAlive, coordFaulty, fwd>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote, coordRequest, coordVote, coordBroadcast, coordDecision, fwd>>

PrededuceCoordinator(p) ==
    /\ coordAlive
    /\ coordBroadcast[p] # waiting
    /\ decision[p] = undecided
    /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

PredecideFromParticipant(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \E q \in participants: fwd[q][p] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Forward(p, q) ==
    /\ alive[p]
    /\ decision[p] # undecided
    /\ fwd[p][q] = notsent
    /\ fwd' = [fwd EXCEPT ![p][q] = decision[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, decision>>

Decide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \A q \in participants: fwd[p][q] # notsent
    /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants: coordBroadcast[q] = waiting
    /\ \A q \in participants: (p = q \/ alive[q]) => fwd[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote, coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote, coordRequest, coordVote, coordBroadcast, coordDecision, coordAlive, coordFaulty, fwd>>

CoordChoice == SendRequest \/ DetectFault \/ MakeDecision \/ BroadcastDecision \/ CoordDie

ParticipantChoice ==
    \/ \E p \in participants: GetVote(p) \/ PrededuceCoordinator(p) \/ PredecideFromParticipant(p) \/ Decide(p) \/ AbortOnTimeout(p) \/ Die(p)
    \/ \E p, q \in participants: Forward(p, q)

NextNB == CoordChoice \/ ParticipantChoice

SpecNB ==
    /\ InitNB
    /\ [][NextNB]_vars
    /\ WF_vars(CoordChoice)
    /\ WF_vars(ParticipantChoice)

Agreement ==
    \A p, q \in participants: (decision[p] = commit) => (decision[q] # abort)

CommitValidity ==
    \A p \in participants: (decision[p] = commit) => (\A q \in participants: vote[q] = yes)

AbortValidity ==
    \A p \in participants: (decision[p] = abort) => (\E q \in participants: vote[q] = no \/ faulty[q] \/ coordFaulty)

Irrevocability ==
    \A p \in participants: (decision[p] = commit \/ decision[p] = abort) ~> (decision[p] = commit \/ decision[p] = abort)

ACP3 ==
    (<> (\A p \in participants: decision[p] # undecided)) \/ (\E p \in participants: faulty[p]) \/ coordFaulty

NonBlockingTermination ==
    \A p \in participants: (alive[p] ~> (decision[p] = commit \/ decision[p] = abort))

====
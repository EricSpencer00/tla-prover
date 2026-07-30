---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, votesent, coordState, forward

vars == <<vote, alive, decision, faulty, votesent, coordState, forward>>

TypeInvNB ==
    /\ vote \in [participants -> {undecided, yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ votesent \in [participants -> BOOLEAN]
    /\ coordState \in {"waiting", "collecting", "decided", "dead"}
    /\ forward \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
    /\ vote = [p \in participants |-> undecided]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ votesent = [p \in participants |-> FALSE]
    /\ coordState = "waiting"
    /\ forward = [p \in participants |-> [q \in participants |-> notsent]]

RequestCoord(p) ==
    /\ coordState = "waiting"
    /\ alive[p]
    /\ coordState' = "collecting"
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, forward>>

VoteCoord(p) ==
    /\ coordState = "collecting"
    /\ vote[p] = undecided
    /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
    /\ votesent' = [votesent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, decision, faulty, coordState, forward>>

CoordFail ==
    /\ coordState \in {"waiting", "collecting"}
    /\ coordState' = "dead"
    /\ faulty' = [p \in participants |-> TRUE]
    /\ UNCHANGED <<vote, alive, decision, votesent, forward>>

DecideCoord(v) ==
    /\ coordState = "collecting"
    /\ \A p \in participants : vote[p] = v
    /\ coordState' = "decided"
    /\ decision' = [p \in participants |-> IF v = yes THEN commit ELSE abort]
    /\ UNCHANGED <<vote, alive, faulty, votesent, forward>>

BroadcastCoord(p) ==
    /\ coordState = "decided"
    /\ alive[p]
    /\ forward["coord"]["coord"] = notsent
    /\ forward' = [forward EXCEPT !["coord"]["coord"] = decision[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, coordState>>

DieCoord ==
    /\ coordState # "dead"
    /\ coordState' = "dead"
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, forward>>

SendVote(p) ==
    /\ coordState = "collecting"
    /\ alive[p]
    /\ vote[p] = undecided
    /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![p] = v]
    /\ votesent' = [votesent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<alive, decision, faulty, coordState, forward>>

AbortVote(p) ==
    /\ coordState = "collecting"
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, votesent, coordState, forward>>

AbortTimeout(p) ==
    /\ decision[p] = undecided
    /\ ~alive[p]
    /\ \A q \in participants : decision[q] = undecided
    /\ \A q \in participants : forward[q][p] = notsent
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, votesent, coordState, forward>>

PreDecideCoord(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ forward["coord"]["coord"] # notsent
    /\ forward' = [forward EXCEPT ![p][p] = forward["coord"]["coord"]]
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, coordState>>

PreDecideForward(p, q) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ forward[q][p] = notsent
    /\ forward[q][q] # notsent
    /\ forward' = [forward EXCEPT ![p][p] = forward[q][q]]
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, coordState>>

Forward(p, q) ==
    /\ alive[p]
    /\ forward[p][p] # notsent
    /\ forward[p][q] = notsent
    /\ forward' = [forward EXCEPT ![p][q] = forward[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent, coordState>>

DecideForwarded(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ \A q \in participants : forward[p][q] # notsent
    /\ forward[p][p] # notsent
    /\ decision' = [decision EXCEPT ![p] = forward[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, votesent, coordState, forward>>

DieParticipant(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, votesent, coordState, forward>>

NextNB ==
    \/ \E p \in participants : RequestCoord(p) \/ SendVote(p) \/ AbortVote(p)
                         \/ AbortTimeout(p) \/ PreDecideCoord(p) \/ DecideForwarded(p)
                         \/ DieParticipant(p)
    \/ \E p \in participants, q \in participants : PreDecideForward(p, q) \/ Forward(p, q)
    \/ CoordFail \/ DieCoord
    \/ \E v \in {yes, no} : DecideCoord(v)
    \/ \E p \in participants : BroadcastCoord(p)

SpecNB ==
    /\ InitNB
    /\ [][NextNB]_vars
    /\ WF_vars(\E p \in participants : PreDecideCoord(p))
    /\ WF_vars(\E p \in participants, q \in participants : Forward(p, q))
    /\ WF_vars(\E p \in participants : DecideForwarded(p))
    /\ WF_vars(\E p \in participants : SendVote(p))

Agreement ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValid ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

AbortValid ==
    \A p, q \in participants :
        (decision[p] = abort /\ decision[q] = commit) => FALSE

Irreversible ==
    \A p \in participants :
        (decision[p] = commit \/ decision[p] = abort) ~> decision[p]

AllDecidedOrFailed ==
    \A p \in participants : (decision[p] # undecided) ~> TRUE

DecideOnRealFault ==
    \E p \in participants :
        (decision[p] = commit => (\A q \in participants : vote[q] = yes))
        /\ (decision[p] = abort =>
                \E q \in participants : vote[q] = no \/ faulty[q] \/ coordState = "dead")

====
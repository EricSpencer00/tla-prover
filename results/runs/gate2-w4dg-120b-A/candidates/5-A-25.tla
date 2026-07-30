---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

NoVote == "NOVOTE"
NoDecision == "NODECISION"

VARIABLES vote, alive, decision, faulty, sentVote, coordRequested, coordVote, coordSent, coordDecision

vars == << vote, alive, decision, faulty, sentVote, coordRequested, coordVote, coordSent, coordDecision >>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ coordRequested \in [participants -> BOOLEAN]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {uncommitted, undecided, commit, abort}

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ coordRequested = [p \in participants |-> FALSE]
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided

SendVoteRequest(p) ==
    /\ alive["coord"]
    /\ ~coordRequested[p]
    /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote, coordVote, coordSent, coordDecision >>

ReceiveVote(p) ==
    /\ alive["coord"]
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ coordVote[p] = waiting
    /\ sentVote[p]
    /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote, coordRequested, coordSent, coordDecision >>

DetectFault(p) ==
    /\ alive["coord"]
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ coordVote[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote, coordRequested, coordVote, coordSent >>

MakeDecision ==
    /\ alive["coord"]
    /\ coordDecision = undecided
    /\ \A p \in participants : coordRequested[p] /\ coordVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote, coordRequested, coordVote, coordSent >>

BroadcastDecision(p) ==
    /\ alive["coord"]
    /\ coordDecision \in {commit, abort}
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote, coordRequested, coordVote, coordDecision >>

SendVote(p) ==
    /\ alive[p]
    /\ coordRequested[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, decision, faulty, coordRequested, coordVote, coordSent, coordDecision >>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, sentVote, coordRequested, coordVote, coordSent, coordDecision >>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordRequested[p]
    /\ ~alive["coord"]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, sentVote, coordRequested, coordVote, coordSent, coordDecision >>

DecideFromCoordinator(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSent[p] \in {commit, abort}
    /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED << vote, alive, faulty, sentVote, coordRequested, coordVote, coordSent, coordDecision >>

DieCoord ==
    /\ alive["coord"]
    /\ ~faulty["coord"]
    /\ alive' = [alive EXCEPT !["coord"] = FALSE]
    /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
    /\ UNCHANGED << vote, decision, sentVote, coordRequested, coordVote, coordSent, coordDecision >>

DieParticipant(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, decision, sentVote, coordRequested, coordVote, coordSent, coordDecision >>

Next ==
    \/ \E p \in participants : SendVoteRequest(p) \/ ReceiveVote(p) \/ DetectFault(p)
    \/ \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideFromCoordinator(p)
    \/ \E p \in participants : DieParticipant(p)
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision(p)
    \/ DieCoord

Spec == Init /\ [][Next]_vars

DecisionAtMostOnce ==
    \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit)

Agreement ==
    ~ \E p, q \in participants : decision[p] = commit /\ decision[q] = abort

CommitValid ==
    \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AbortValid ==
    \A p \in participants : decision[p] = abort => ( (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ faulty["coord"] )

EventuallyDecide ==
    \A p \in participants : (decision[p] = undecided) ~> (decision[p] # undecided \/ faulty[p] \/ faulty["coord"])

====
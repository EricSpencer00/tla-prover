---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, coordAsked, coordVote, coordSent, coordDecision, coordAlive

vars == <<vote, alive, decision, faulty, voted, coordAsked, coordVote, coordSent, coordDecision, coordAlive>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants \cup {"coord"} -> BOOLEAN]
    /\ voted \in [participants -> BOOLEAN]
    /\ coordAsked \in [participants -> BOOLEAN]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants \cup {"coord"} |-> FALSE]
    /\ voted = [p \in participants |-> FALSE]
    /\ coordAsked = [p \in participants |-> FALSE]
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE

SendRequest(p) ==
    /\ coordAlive
    /\ ~coordAsked[p]
    /\ coordAsked' = [coordAsked EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordVote, coordSent, coordDecision>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordAsked[p]
    /\ coordVote[p] = waiting
    /\ voted[p]
    /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordAsked, coordSent, coordDecision, coordAlive>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordAsked[p]
    /\ coordVote[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordAsked, coordVote, coordSent, coordAlive>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordAsked, coordVote, coordSent, coordAlive>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordAsked, coordVote, coordDecision, coordAlive>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ faulty' = [faulty EXCEPT !["coord"] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, voted, coordAsked, coordVote, coordSent, coordDecision>>

SendVote(p) ==
    /\ alive[p]
    /\ coordAsked[p]
    /\ ~voted[p]
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, coordAsked, coordVote, coordSent, coordDecision, coordAlive>>

AbortOnNo(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ voted[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voted, coordAsked, coordVote, coordSent, coordDecision, coordAlive>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~coordAsked[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voted, coordAsked, coordVote, coordSent, coordDecision, coordAlive>>

DecideOnBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSent[p] \in {commit, abort}
    /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<vote, alive, faulty, voted, coordAsked, coordVote, coordSent, coordDecision, coordAlive>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, voted, coordAsked, coordVote, coordSent, coordDecision, coordAlive>>

Next ==
    \/ \E p \in participants : SendRequest(p) \/ ReceiveVote(p) \/ DetectFault(p)
    \/ \E p \in participants : SendVote(p) \/ AbortOnNo(p) \/ AbortOnTimeout(p) \/ DecideOnBroadcast(p) \/ ParticipantDie(p)
    \/ \E p \in participants : BroadcastDecision(p)
    \/ MakeDecision
    \/ CoordDie

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in participants : WF_vars(SendVote(p)) /\ WF_vars(DecideOnBroadcast(p))
    /\ WF_vars(MakeDecision)
    /\ WF_vars(CoordDie)

Agreement ==
    \A i, j \in participants : ~(decision[i] = commit /\ decision[j] = abort)

CommitValidity ==
    \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

AbortValidity ==
    \E p \in participants : decision[p] = abort =>
        \/ \E q \in participants : vote[q] = no
        \/ \E q \in participants : faulty[q]
        \/ faulty["coord"]

Irreversibility ==
    /\ \A p \in participants : (decision[p] = commit) ~> (decision[p] = commit)
    /\ \A p \in participants : (decision[p] = abort) ~> (decision[p] = abort)

EventuallyDecide ==
    <>(\A p \in participants : decision[p] \in {commit, abort} \/ faulty[p] \/ faulty["coord"])

====
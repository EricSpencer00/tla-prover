---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, votesent,
          coordRequested, coordVotes, coordSent, coordDecision, coordAlive

vars == <<vote, alive, decision, faulty, votesent,
           coordRequested, coordVotes, coordSent, coordDecision, coordAlive>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants \cup {coordDecision} -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants \cup {coordDecision} -> BOOLEAN]
    /\ votesent \subseteq participants
    /\ coordRequested \subseteq participants
    /\ coordVotes \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants \cup {coordDecision} |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants \cup {coordDecision} |-> FALSE]
    /\ votesent = {}
    /\ coordRequested = {}
    /\ coordVotes = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE

\* Coordinator actions
RequestVote(p) ==
    /\ coordAlive
    /\ p \notin coordRequested
    /\ coordRequested' = coordRequested \cup {p}
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                   coordVotes, coordSent, coordDecision>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in coordRequested
    /\ coordVotes[p] = waiting
    /\ p \in votesent
    /\ coordVotes' = [coordVotes EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                   coordRequested, coordSent, coordDecision, coordAlive>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ p \in coordRequested
    /\ coordVotes[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                   coordRequested, coordVotes, coordSent, coordAlive>>

CoordDecide ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested = participants
    /\ \A p \in participants : coordVotes[p] # waiting
    /\ coordDecision' = IF \A p \in participants : vote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                   coordRequested, coordVotes, coordSent, coordAlive>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, votesent,
                   coordRequested, coordVotes, coordDecision, coordAlive>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ faulty' = [faulty EXCEPT ![coordDecision] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, votesent,
                   coordRequested, coordVotes, coordSent, coordDecision>>

\* Participant actions
SendVote(p) ==
    /\ alive[p]
    /\ p \in coordRequested
    /\ p \notin votesent
    /\ votesent' = votesent \cup {p}
    /\ UNCHANGED <<vote, alive, decision, faulty,
                   coordRequested, coordVotes, coordSent, coordDecision, coordAlive>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ p \in votesent
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, votesent,
                   coordRequested, coordVotes, coordSent, coordDecision, coordAlive>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ p \notin coordRequested
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, votesent,
                   coordRequested, coordVotes, coordSent, coordDecision, coordAlive>>

DecideOnBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<vote, alive, faulty, votesent,
                   coordRequested, coordVotes, coordSent, coordDecision, coordAlive>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, votesent,
                   coordRequested, coordVotes, coordSent, coordDecision, coordAlive>>

Next ==
    \/ \E p \in participants : RequestVote(p)
    \/ \E p \in participants : CoordReceiveVote(p)
    \/ \E p \in participants : CoordDetectFault(p)
    \/ CoordDecide
    \/ \E p \in participants : BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideOnBroadcast(p)
    \/ \E p \in participants : ParticipantDie(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : SendVote(p))
    /\ WF_vars(\E p \in participants : BroadcastDecision(p))
    /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))

AC1 ==
    \A p1 \in participants, p2 \in participants :
        (decision[p1] = commit /\ decision[p2] = abort) => (p1 = p2)

AC2 ==
    \A p \in participants : decision[p] = commit => (\A q \in participants : vote[q] = yes)

AC3 ==
    \A p \in participants : decision[p] = abort =>
        (\E q \in participants : vote[q] = no) \/ (\E q \in participants : faulty[q]) \/ faulty[coordDecision]

AC4 ==
    \A p \in participants :
        /\ decision[p] = commit => (decision[p] = commit)
        /\ decision[p] = abort => (decision[p] = abort)

AC3eventually ==
    <> (\A p \in participants : decision[p] # undecided) \/ (\E p \in participants : faulty[p]) \/ faulty[coordDecision]

====
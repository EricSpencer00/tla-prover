---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote
VARIABLES coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sentVote,
          coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ coordRequested \in [participants -> BOOLEAN]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ \E v \in [participants -> {yes, no}]:
        vote = v
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ coordRequested = [p \in participants |-> FALSE]
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

SendVoteRequest(p) ==
    /\ coordAlive
    /\ ~coordRequested[p]
    /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordVote, coordSent, coordDecision, coordFaulty>>

RecvVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ coordVote[p] = waiting
    /\ sentVote[p]
    /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordRequested, coordSent, coordDecision, coordAlive, coordFaulty>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ coordVote[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordRequested, coordVote, coordSent, coordAlive, coordFaulty>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: coordVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants: coordVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordRequested, coordVote, coordSent, coordAlive, coordFaulty>>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordRequested, coordVote, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sentVote,
                 coordRequested, coordVote, coordSent, coordDecision>>

SendVote(p) ==
    /\ alive[p]
    /\ coordRequested[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty,
                 coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~coordRequested[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

Decide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<vote, alive, faulty, sentVote,
                 coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

Die(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sentVote,
                 coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants: SendVoteRequest(p)
    \/ \E p \in participants: RecvVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: Die(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(SendVoteRequest(participants[1]))
        /\ WF_vars(SendVote(participants[1]))
        /\ WF_vars(AbortOnVote(participants[1]))
        /\ WF_vars(Decide(participants[1]))

CommitAgree ==
    \A p, q \in participants:
        (decision[p] = commit /\ decision[q] = abort) => p = q

CommitValid ==
    \A p \in participants: decision[p] = commit => \A q \in participants: vote[q] = yes

AbortValid ==
    \A p \in participants: decision[p] = abort =>
        \/ \E q \in participants: vote[q] = no
        \/ \E q \in participants: faulty[q]
        \/ coordFaulty

Irreversible ==
    \A p \in participants: (decision[p] = commit) ~> (decision[p] = commit)
        /\ (decision[p] = abort) ~> (decision[p] = abort)

EventuallyDecideOrFault ==
    <>(\A p \in participants: decision[p] # undecided) \/ (\E p \in participants: faulty[p]) \/ coordFaulty

====
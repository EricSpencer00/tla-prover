---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, coordRequested, coordVote,
         coordSent, coordDecision, coordAlive

vars == <<vote, alive, decision, faulty, voted, coordRequested, coordVote,
          coordSent, coordDecision, coordAlive>>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voted \in [participants -> BOOLEAN]
    /\ coordRequested \in [participants -> BOOLEAN]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {notSent, sent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN

Init ==
    /\ \A p \in participants: vote' [p] = CHOOSE v \in {yes, no} : TRUE
    /\ \A p \in participants: alive' [p] = TRUE
    /\ \A p \in participants: decision' [p] = undecided
    /\ \A p \in participants: faulty' [p] = FALSE
    /\ \A p \in participants: voted' [p] = FALSE
    /\ \A p \in participants: coordRequested' [p] = FALSE
    /\ \A p \in participants: coordVote' [p] = waiting
    /\ \A p \in participants: coordSent' [p] = notSent
    /\ coordDecision' = undecided
    /\ coordAlive' = TRUE

SendVoteRequest(p) ==
    /\ coordAlive
    /\ ~coordRequested [p]
    /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordVote,
                  coordSent, coordDecision, coordAlive>>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested [p]
    /\ coordVote [p] = waiting
    /\ voted [p]
    /\ coordVote' = [coordVote EXCEPT ![p] = vote [p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                  coordSent, coordDecision, coordAlive>>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested [p]
    /\ coordVote [p] = waiting
    /\ ~alive [p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                  coordVote, coordSent, coordAlive>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: coordVote [p] # waiting
    /\ coordDecision' = IF \A p \in participants: coordVote [p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                  coordVote, coordSent, coordAlive>>

BroadcastDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent [p] = notSent
    /\ coordSent' = [coordSent EXCEPT ![p] = sent]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                  coordVote, coordDecision, coordAlive>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ faulty' = [q \in participants |-> faulty [q]]
    /\ UNCHANGED <<vote, alive, decision, voted, coordRequested,
                  coordVote, coordSent, coordDecision>>

SendVote(p) ==
    /\ alive [p]
    /\ coordRequested [p]
    /\ ~voted [p]
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, coordRequested,
                  coordVote, coordSent, coordDecision, coordAlive>>

AbortOnVote(p) ==
    /\ alive [p]
    /\ decision [p] = undecided
    /\ voted [p]
    /\ vote [p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voted, coordRequested,
                  coordVote, coordSent, coordDecision, coordAlive>>

AbortOnTimeout(p) ==
    /\ alive [p]
    /\ decision [p] = undecided
    /\ ~coordAlive
    /\ ~coordRequested [p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voted, coordRequested,
                  coordVote, coordSent, coordDecision, coordAlive>>

DecideFromBroadcast(p) ==
    /\ alive [p]
    /\ decision [p] = undecided
    /\ coordSent [p] = sent
    /\ decision' = [decision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, faulty, voted, coordRequested,
                  coordVote, coordSent, coordDecision, coordAlive>>

Die(p) ==
    /\ alive [p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, voted, coordRequested,
                  coordVote, coordSent, coordDecision, coordAlive>>

Next ==
    \/ \E p \in participants: SendVoteRequest(p)
    \/ \E p \in participants: ReceiveVote(p)
    \/ \E p \in participants: DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants: BroadcastDecision(p)
    \/ CoordDie
    \/ \E p \in participants: SendVote(p)
    \/ \E p \in participants: AbortOnVote(p)
    \/ \E p \in participants: AbortOnTimeout(p)
    \/ \E p \in participants: DecideFromBroadcast(p)
    \/ \E p \in participants: Die(p)

Spec == Init /\ [][Next]_vars
        /\ \A p \in participants: WF_vars(SendVote(p))
        /\ \A p \in participants: WF_vars(DecideFromBroadcast(p))
        /\ WF_vars(MakeDecision)

AC1 ==
    \A p, q \in participants: (decision [p] = commit /\ decision [q] = abort) => FALSE

AC2 ==
    \A p \in participants: decision [p] = commit => \A q \in participants: vote [q] = yes

AC3 ==
    \A p \in participants: decision [p] = abort =>
        \/ \E q \in participants: vote [q] = no
        \/ \E q \in participants: faulty [q]
        \/ ~coordAlive

AC4 ==
    \A p \in participants:
        /\ (decision [p] = commit => decision' [p] = commit)
        /\ (decision [p] = abort => decision' [p] = abort)

\* Simple broadcast can block, so AC5 (every non-faulty participant eventually decides)
\* does NOT hold, and is therefore omitted from the spec.
EventuallySomeDecide ==
    <>(\E p \in participants: decision [p] # undecided) \/ <>(~coordAlive \/ \E q \in participants: faulty [q])

====
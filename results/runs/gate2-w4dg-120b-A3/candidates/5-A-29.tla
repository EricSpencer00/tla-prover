---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, voted, coordRequested, coordRecv, coordSent, coordDecision,
    coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, voted, coordRequested, coordRecv, coordSent,
    coordDecision, coordAlive, coordFaulty>>

TypeOK ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ voted \subseteq participants
    /\ coordRequested \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ voted = {}
    /\ coordRequested = [p \in participants |-> FALSE]
    /\ coordRecv = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

CoordSendReq(p) ==
    /\ coordAlive
    /\ ~coordRequested[p]
    /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRecv,
                   coordSent, coordDecision, coordAlive, coordFaulty>>

CoordReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ coordRecv[p] = waiting
    /\ p \in voted
    /\ coordRecv' = [coordRecv EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                   coordSent, coordDecision, coordAlive, coordFaulty>>

CoordDetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ coordRecv[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                   coordRecv, coordSent, coordAlive, coordFaulty>>

CoordDecide ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: coordRequested[p] /\ coordRecv[p] # waiting
    /\ coordDecision' = IF \A p \in participants: coordRecv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                   coordRecv, coordSent, coordAlive, coordFaulty>>

CoordBroadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                   coordRecv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, voted, coordRequested,
                   coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

ParticipantSendVote(p) ==
    /\ alive[p]
    /\ coordRequested[p]
    /\ p \notin voted
    /\ voted' = voted \cup {p}
    /\ UNCHANGED <<vote, alive, decision, faulty, coordRequested,
                   coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

ParticipantAbortOnNo(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ p \in voted
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voted, coordRequested,
                   coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

ParticipantAbortOnLostReq(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordRequested[p]
    /\ ~coordAlive
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, voted, coordRequested,
                   coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

ParticipantDecide(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSent[p] \in {commit, abort}
    /\ decision' = [decision EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<vote, alive, faulty, voted, coordRequested,
                   coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, voted, coordRequested,
                   coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants: CoordSendReq(p)
    \/ \E p \in participants: CoordReceiveVote(p)
    \/ \E p \in participants: CoordDetectFault(p)
    \/ CoordDecide
    \/ \E p \in participants: CoordBroadcast(p)
    \/ CoordDie
    \/ \E p \in participants: ParticipantSendVote(p)
    \/ \E p \in participants: ParticipantAbortOnNo(p)
    \/ \E p \in participants: ParticipantAbortOnLostReq(p)
    \/ \E p \in participants: ParticipantDecide(p)
    \/ \E p \in participants: ParticipantDie(p)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants: ParticipantSendVote(p))
    /\ WF_vars(\E p \in participants: ParticipantAbortOnNo(p))
    /\ WF_vars(\E p \in participants: ParticipantDecide(p))
    /\ WF_vars(CoordDecide)
    /\ WF_vars(\E p \in participants: CoordBroadcast(p))

NoParticipantDecidesDifferently ==
    \A p1, p2 \in participants:
        (decision[p1] = commit /\ decision[p2] = abort) => FALSE

DecidingCommitMeansAllVotedYes ==
    \A p \in participants: decision[p] = commit => \A q \in participants: vote[q] = yes

DecidingAbortMeansNoVoteOrFault ==
    \A p \in participants: decision[p] = abort =>
        \/ \E q \in participants: vote[q] = no
        \/ \E q \in participants: faulty[q]
        \/ coordFaulty

DecisionIsIrreversible ==
    \A p \in participants:
        /\ (decision[p] = commit => decision' = [decision EXCEPT ![p] = commit])
        /\ (decision[p] = abort => decision' = [decision EXCEPT ![p] = abort])

SomeDecisionOrParticipantFault ==
    \E p \in participants:
        decision[p] # undecided \/ faulty[p] \/ coordFaulty

EventuallyDecideOrDetectFault ==
    <>(SomeDecisionOrParticipantFault)

====
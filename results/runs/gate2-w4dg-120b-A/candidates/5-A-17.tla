---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sentVote,
         coordRequested, coordVote, coordSentDecision,
         coordDecision, coordAlive, coordFaulty

vars == << vote, alive, decision, faulty, sentVote,
           coordRequested, coordVote, coordSentDecision,
           coordDecision, coordAlive, coordFaulty >>

TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ coordRequested \in [participants -> BOOLEAN]
    /\ coordVote \in [participants -> {yes, no, waiting}]
    /\ coordSentDecision \in [participants -> {notsent, commit, abort}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ coordRequested = [p \in participants |-> FALSE]
    /\ coordVote = [p \in participants |-> waiting]
    /\ coordSentDecision = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

SendRequest(p) ==
    /\ coordAlive
    /\ ~coordRequested[p]
    /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                   coordVote, coordSentDecision,
                   coordDecision, coordAlive, coordFaulty >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : coordRequested[q]
    /\ coordVote[p] = waiting
    /\ sentVote[p]
    /\ coordVote' = [coordVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                   coordRequested, coordSentDecision,
                   coordDecision, coordAlive, coordFaulty >>

DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A q \in participants : coordRequested[q]
    /\ coordVote[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                   coordRequested, coordVote, coordSentDecision,
                   coordAlive, coordFaulty >>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordVote[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                   coordRequested, coordVote, coordSentDecision,
                   coordAlive, coordFaulty >>

Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSentDecision[p] = notsent
    /\ coordSentDecision' = [coordSentDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                   coordRequested, coordVote,
                   coordDecision, coordAlive, coordFaulty >>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                   coordRequested, coordVote,
                   coordSentDecision, coordDecision, coordAlive, coordFaulty >>

ParticipantSendVote(p) ==
    /\ alive[p]
    /\ coordRequested[p]
    /\ ~sentVote[p]
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, alive, decision, faulty,
                   coordRequested, coordVote, coordSentDecision,
                   coordDecision, coordAlive, coordFaulty >>

ParticipantAbortOnNo(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, sentVote,
                   coordRequested, coordVote,
                   coordSentDecision, coordDecision,
                   coordAlive, coordFaulty >>

ParticipantAbortOnRequestTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ ~coordRequested[p]
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, alive, faulty, sentVote,
                   coordRequested, coordVote,
                   coordSentDecision, coordDecision,
                   coordAlive, coordFaulty >>

DecideFromCoordinator(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSentDecision[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = coordSentDecision[p]]
    /\ UNCHANGED << vote, alive, faulty, sentVote,
                   coordRequested, coordVote,
                   coordSentDecision, coordDecision,
                   coordAlive, coordFaulty >>

ParticipantDie(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, decision, sentVote,
                   coordRequested, coordVote,
                   coordSentDecision, coordDecision,
                   coordAlive, coordFaulty >>

Next ==
    \/ \E p \in participants : SendRequest(p) \/ ReceiveVote(p) \/ DetectFault(p)
                            \/ Broadcast(p) \/ ParticipantSendVote(p) \/ ParticipantAbortOnNo(p)
                            \/ ParticipantAbortOnRequestTimeout(p) \/ DecideFromCoordinator(p)
                            \/ ParticipantDie(p)
    \/ MakeDecision
    \/ CoordDie

Spec == Init /\ [][Next]_vars
    /\ UNCHANGED << vote >>

\* Safety: no two participants ever disagree (commit vs. abort).
\* Safety: a committed decision is only possible if everyone voted yes.
\* Safety: an aborted decision is only possible due to a no vote or a failure.
\* Safety: each participant decides at most once (irrevocably).
AC1 ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

AC2 ==
    \A p \in participants :
        decision[p] = commit => \A q \in participants : vote[q] = yes

AC3 ==
    \A p \in participants :
        decision[p] = abort =>
            \/ (\E q \in participants : vote[q] = no)
            \/ (\E q \in participants : faulty[q])
            \/ coordFaulty

AC4 ==
    \A p \in participants :
        \A s \in {commit, abort} : (decision[p] = s) ~> (decision[p] = s)

\* Liveness: every transaction eventually resolves or is acknowledged as failed.
\* The simple-broadcast variant does NOT guarantee every non-faulty participant decides.
NoUndecided ==
    (\A p \in participants : decision[p] # undecided)
    \/ (\E p \in participants : faulty[p])
    \/ coordFaulty

====
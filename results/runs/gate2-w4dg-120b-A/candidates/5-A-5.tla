---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pcVote, pcAlive, pcDecision, pcFaulty, pcSent
VARIABLES vote, alive, decision, faulty, sentVote, coordSent

vars == <<pcVote, pcAlive, pcDecision, pcFaulty, pcSent,
          vote, alive, decision, faulty, sentVote, coordSent>>

TypeInv ==
    /\ pcVote \in [participants -> {yes, no, waiting}]
    /\ pcAlive \in BOOLEAN
    /\ pcDecision \in {commit, abort, undecided}
    /\ pcFaulty \in BOOLEAN
    /\ pcSent \in [participants -> {waiting, notsent}]
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {commit, abort, undecided}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ coordSent \in [participants -> {waiting, notsent}]

Init ==
    /\ pcVote = [p \in participants |-> waiting]
    /\ pcAlive = TRUE
    /\ pcDecision = undecided
    /\ pcFaulty = FALSE
    /\ pcSent = [p \in participants |-> waiting]
    /\ vote = [p \in participants |-> IF TRUE THEN yes ELSE no]
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ coordSent = [p \in participants |-> waiting]

\* Simple broadcast: send a vote request to a live participant.
SendVoteReq(p) ==
    /\ pcAlive
    /\ pcSent[p] = waiting
    /\ pcSent' = [pcSent EXCEPT ![p] = notsent]
    /\ UNCHANGED <<pcVote, pcAlive, pcDecision, pcFaulty,
                   vote, alive, decision, faulty, sentVote, coordSent>>

\* Receive a participant's vote at the coordinator.
ReceiveVote(p) ==
    /\ pcAlive
    /\ pcDecision = undecided
    /\ \A q \in participants : pcSent[q] # waiting
    /\ pcVote[p] = waiting
    /\ sentVote[p]
    /\ pcVote' = [pcVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<pcAlive, pcDecision, pcFaulty, pcSent,
                   vote, alive, decision, faulty, sentVote, coordSent>>

\* Detect a participant that died without voting: abort.
DetectFault(p) ==
    /\ pcAlive
    /\ pcDecision = undecided
    /\ \A q \in participants : pcSent[q] # waiting
    /\ pcVote[p] = waiting
    /\ ~alive[p]
    /\ pcDecision' = abort
    /\ UNCHANGED <<pcVote, pcAlive, pcFaulty, pcSent,
                   vote, alive, decision, faulty, sentVote, coordSent>>

\* Commit only if all votes are yes; otherwise abort.
MakeDecision ==
    /\ pcAlive
    /\ pcDecision = undecided
    /\ \A p \in participants : pcVote[p] # waiting
    /\ pcDecision' = IF \A p \in participants : pcVote[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pcVote, pcAlive, pcFaulty, pcSent,
                   vote, alive, decision, faulty, sentVote, coordSent>>

\* Send the coordinator's decision to a participant (simple broadcast).
BroadcastDecision(p) ==
    /\ pcAlive
    /\ pcDecision # undecided
    /\ coordSent[p] = waiting
    /\ coordSent' = [coordSent EXCEPT ![p] = notsent]
    /\ UNCHANGED <<pcVote, pcAlive, pcDecision, pcFaulty, pcSent,
                   vote, alive, decision, faulty, sentVote>>

DieCoordinator ==
    /\ pcAlive
    /\ pcAlive' = FALSE
    /\ pcFaulty' = TRUE
    /\ UNCHANGED <<pcVote, pcDecision, pcSent,
                   vote, alive, decision, faulty, sentVote, coordSent>>

\* A participant sends its vote to the coordinator.
SendVote(p) ==
    /\ alive[p]
    /\ pcSent[p] = notsent
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pcVote, pcAlive, pcDecision, pcFaulty, pcSent,
                   vote, alive, decision, faulty, coordSent>>

\* A participant that voted no aborts unilaterally.
AbortOnVote(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sentVote[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pcVote, pcAlive, pcDecision, pcFaulty, pcSent,
                   vote, alive, faulty, sentVote, coordSent>>

\* A participant times out because the coordinator died: abort.
AbortOnCoordFailure(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~pcAlive
    /\ pcSent[p] = waiting
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<pcVote, pcAlive, pcDecision, pcFaulty, pcSent,
                   vote, alive, faulty, sentVote, coordSent>>

\* A participant adopts the coordinator's decision.
DecideOnBroadcast(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordSent[p] = notsent
    /\ decision' = [decision EXCEPT ![p] = pcDecision]
    /\ UNCHANGED <<pcVote, pcAlive, pcDecision, pcFaulty, pcSent,
                   vote, alive, faulty, sentVote, coordSent>>

DieParticipant(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pcVote, pcAlive, pcDecision, pcFaulty, pcSent,
                   vote, decision, sentVote, coordSent>>

CoordinatorProgress ==
    \/ \E p \in participants : SendVoteReq(p) \/ ReceiveVote(p)
                              \/ DetectFault(p) \/ BroadcastDecision(p)
    \/ MakeDecision \/ DieCoordinator

ParticipantProgress ==
    \E p \in participants :
        \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnCoordFailure(p)
        \/ DecideOnBroadcast(p) \/ DieParticipant(p)

Next ==
    \/ CoordinatorProgress
    \/ ParticipantProgress

\* Fairness: progress actions happen eventually; death is not.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CoordinatorProgress)
    /\ WF_vars(ParticipantProgress)

\* No two participants decide differently.
AC1 ==
    \A p, q \in participants :
        (decision[p] = commit /\ decision[q] = abort) => FALSE

\* Commit only if all voted yes.
AC2 ==
    \A p \in participants :
        decision[p] = commit => \A q \in participants : vote[q] = yes

\* Abort only if a vote no or a fault exists.
AC3 ==
    \A p \in participants :
        decision[p] = abort =>
            (\E q \in participants : vote[q] = no \/ faulty[q]) \/ pcFaulty

\* A participant never decides twice.
AC4 ==
    \A p \in participants :
        /\ (decision[p] = commit => decision[p]' = commit)
        /\ (decision[p] = abort => decision[p]' = abort)

\* Eventual resolution or fault (the blocking protocol does not guarantee all
\* non-faulty participants decide, so termination is not guaranteed here).
FinalResolution ==
    \E p \in participants : decision[p] = commit
        \/ \E p \in participants : decision[p] = abort
        \/ \E p \in participants : faulty[p]
        \/ pcFaulty

====
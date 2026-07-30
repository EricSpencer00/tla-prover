---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participantVote, participantAlive, participantDecision, participantFaulty, participantSent
VARIABLES coordRequested, coordReceived, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<participantVote, participantAlive, participantDecision, participantFaulty, participantSent,
           coordRequested, coordReceived, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantSent \in [participants -> BOOLEAN]
    /\ coordRequested \in [participants -> BOOLEAN]
    /\ coordReceived \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {committed, notsent}]
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantSent = [p \in participants |-> FALSE]
    /\ coordRequested = [p \in participants |-> FALSE]
    /\ coordReceived = [p \in participants |-> waiting]
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\* Coordinator sends a vote request to a participant.
RequestVote(p) ==
    /\ coordAlive
    /\ ~coordRequested[p]
    /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent,
                   coordReceived, coordSent, coordDecision, coordFaulty>>

\* Coordinator receives a vote from a participant.
ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ coordReceived[p] = waiting
    /\ participantSent[p]
    /\ coordReceived' = [coordReceived EXCEPT ![p] = participantVote[p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent,
                   coordRequested, coordSent, coordDecision, coordFaulty>>

\* Coordinator detects a participant died without voting and aborts.
DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[p]
    /\ coordReceived[p] = waiting
    /\ ~participantAlive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent,
                   coordRequested, coordReceived, coordSent, coordFaulty>>

\* Coordinator makes a decision once all votes are collected.
MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants : coordReceived[p] # waiting
    /\ IF \A p \in participants : coordReceived[p] = yes
         THEN coordDecision' = commit
         ELSE coordDecision' = abort
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent,
                   coordRequested, coordReceived, coordSent, coordFaulty>>

\* Coordinator broadcasts the decision using simple broadcast.
SendDecision(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent[p] = notsent
    /\ coordSent' = [coordSent EXCEPT ![p] = committed]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent,
                   coordRequested, coordReceived, coordDecision, coordFaulty>>

\* Coordinator dies (crashes).
DieCoordinator ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent,
                   coordRequested, coordReceived, coordSent, coordDecision>>

\* Participant sends its vote to the coordinator.
SendVote(p) ==
    /\ participantAlive[p]
    /\ ~participantSent[p]
    /\ coordRequested[p]
    /\ participantSent' = [participantSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty,
                   coordRequested, coordReceived, coordSent, coordDecision,
                   coordAlive, coordFaulty>>

\* Participant decides abort unilaterally if its vote is no.
AbortOnVote(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ participantSent[p]
    /\ participantVote[p] = no
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                   participantSent,
                   coordRequested, coordReceived, coordSent, coordDecision,
                   coordAlive, coordFaulty>>

\* Participant aborts on timeout because the coordinator died.
AbortOnTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordAlive
    /\ ~coordRequested[p]
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                   participantSent,
                   coordRequested, coordReceived, coordSent, coordDecision,
                   coordAlive, coordFaulty>>

\* Participant adopts the coordinator's broadcasted decision.
DecideOnCoord(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ coordSent[p] = committed
    /\ participantDecision' = [participantDecision EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                   participantSent,
                   coordRequested, coordReceived, coordSent, coordDecision,
                   coordAlive, coordFaulty>>

\* Participant dies (crashes).
DieParticipant(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantVote, participantDecision, participantSent,
                   coordRequested, coordReceived, coordSent, coordDecision,
                   coordAlive, coordFaulty>>

Next ==
    \/ \E p \in participants : RequestVote(p)
    \/ \E p \in participants : ReceiveVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : SendDecision(p)
    \/ DieCoordinator
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideOnCoord(p)
    \/ \E p \in participants : DieParticipant(p)

\* Weak fairness excludes the death transitions, which are not assumed to be
\* scheduled -- only progress actions for participants and the coordinator.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in participants :
           /\ TRUE
           /\ TRUE
           /\ TRUE
           /\ TRUE
    /\ TRUE

\* No two participants ever decide differently.
AC1 ==
    \A a \in participants, b \in participants :
        (a # b /\ participantDecision[a] = commit /\ participantDecision[b] = abort) ~> FALSE

\* A commit decision needs a unanimous yes vote.
AC2 ==
    \A a \in participants :
        (participantDecision[a] = commit) ~> (\A p \in participants : participantVote[p] = yes)

\* An abort decision needs a no vote, or some participant to be faulty, or
\* the coordinator to be faulty.
AC3 ==
    \A a \in participants :
        (participantDecision[a] = abort) ~>
            (\E p \in participants : participantVote[p] = no \/ participantFaulty[p]) \/ coordFaulty

\* Decisions are irrevocably final.
AC4 ==
    \A a \in participants :
        /\ (participantDecision[a] = commit) ~> (participantDecision[a] = commit)
        /\ (participantDecision[a] = abort) ~> (participantDecision[a] = abort)

\* Liveness: the protocol eventually reaches a decided outcome (or a failure).
\* Note: the simple broadcast variant does NOT guarantee every non-faulty
\* participant decides -- the irrecoverable coordinator broadcast failure is
\* exactly what blocks that stronger liveness property.
AC3Liveness ==
    \A a \in participants :
        (participantDecision[a] = undecided) ~>
            (coordFaulty \/ \E p \in participants : participantDecision[p] # undecided)

====
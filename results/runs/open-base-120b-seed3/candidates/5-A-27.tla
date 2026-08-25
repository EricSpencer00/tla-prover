---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    participants, \* set of participants
    yes, no,         \* vote values
    undecided, commit, abort, \* decision values
    waiting, notsent \* auxiliary constants used in types

\* ----------------------------------------------------------------------
\* State Variables
\* ----------------------------------------------------------------------
VARIABLES
    Vote,            \* Vote[p] ∈ {yes, no}
    SentVote,        \* SentVote[p] ∈ BOOLEAN (TRUE if p has sent its vote)
    Decision,        \* Decision[p] ∈ {undecided, commit, abort}
    Alive,           \* Alive[p] ∈ BOOLEAN
    Faulty,          \* Faulty[p] ∈ BOOLEAN
    RequestSent,     \* RequestSent[p] ∈ BOOLEAN (coordinator has sent request)
    ReceivedVote,    \* ReceivedVote[p] ∈ {yes, no, waiting}
    BroadcastSent,   \* BroadcastSent[p] ∈ BOOLEAN (coordinator broadcasted decision)
    CoordDecision,   \* CoordDecision ∈ {undecided, commit, abort}
    CoordAlive,      \* CoordAlive ∈ BOOLEAN
    CoordFaulty      \* CoordFaulty ∈ BOOLEAN

vars == << Vote, SentVote, Decision, Alive, Faulty,
           RequestSent, ReceivedVote, BroadcastSent,
           CoordDecision, CoordAlive, CoordFaulty >>

\* ----------------------------------------------------------------------
\* Initial State
\* ----------------------------------------------------------------------
Init ==
    /\ Vote = [p \in participants |-> IF RandomChoice({yes, no}) = yes THEN yes ELSE no]
    /\ SentVote = [p \in participants |-> FALSE]
    /\ Decision = [p \in participants |-> undecided]
    /\ Alive = [p \in participants |-> TRUE]
    /\ Faulty = [p \in participants |-> FALSE]
    /\ RequestSent = [p \in participants |-> FALSE]
    /\ ReceivedVote = [p \in participants |-> waiting]
    /\ BroadcastSent = [p \in participants |-> FALSE]
    /\ CoordDecision = undecided
    /\ CoordAlive = TRUE
    /\ CoordFaulty = FALSE

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
AllRequestsSent ==
    \A p \in participants : RequestSent[p] = TRUE

AllVotesReceived ==
    \A p \in participants : ReceivedVote[p] \in {yes, no}

AllVotesYes ==
    \A p \in participants : ReceivedVote[p] = yes

AllDecided ==
    \A p \in participants : Decision[p] # undecided

\* ----------------------------------------------------------------------
\* Coordinator Actions
\* ----------------------------------------------------------------------
SendReq(p) ==
    /\ CoordAlive
    /\ RequestSent[p] = FALSE
    /\ RequestSent' = [RequestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << Vote, SentVote, Decision, Alive, Faulty,
                    ReceivedVote, BroadcastSent,
                    CoordDecision, CoordAlive, CoordFaulty >>

RecvVote(p) ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ AllRequestsSent
    /\ ReceivedVote[p] = waiting
    /\ SentVote[p] = TRUE
    /\ ReceivedVote' = [ReceivedVote EXCEPT ![p] = Vote[p]]
    /\ UNCHANGED << Vote, SentVote, Decision, Alive, Faulty,
                    RequestSent, BroadcastSent,
                    CoordDecision, CoordAlive, CoordFaulty >>

DetectFault(p) ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ AllRequestsSent
    /\ ReceivedVote[p] = waiting
    /\ Alive[p] = FALSE
    /\ SentVote[p] = FALSE
    /\ CoordDecision' = abort
    /\ UNCHANGED << Vote, SentVote, Decision, Alive, Faulty,
                    RequestSent, ReceivedVote, BroadcastSent,
                    CoordAlive, CoordFaulty >>

MakeDecision ==
    /\ CoordAlive
    /\ CoordDecision = undecided
    /\ AllVotesReceived
    /\ IF AllVotesYes
          THEN CoordDecision' = commit
          ELSE CoordDecision' = abort
    /\ UNCHANGED << Vote, SentVote, Decision, Alive, Faulty,
                    RequestSent, ReceivedVote, BroadcastSent,
                    CoordAlive, CoordFaulty >>

Broadcast(p) ==
    /\ CoordAlive
    /\ CoordDecision # undecided
    /\ BroadcastSent[p] = FALSE
    /\ BroadcastSent' = [BroadcastSent EXCEPT ![p] = TRUE]
    /\ Decision' = [Decision EXCEPT ![p] = CoordDecision]
    /\ UNCHANGED << Vote, SentVote, Alive, Faulty,
                    RequestSent, ReceivedVote,
                    CoordDecision, CoordAlive, CoordFaulty >>

CoordDie ==
    /\ CoordAlive
    /\ CoordAlive' = FALSE
    /\ CoordFaulty' = TRUE
    /\ UNCHANGED << Vote, SentVote, Decision, Alive, Faulty,
                    RequestSent, ReceivedVote, BroadcastSent,
                    CoordDecision >>

\* ----------------------------------------------------------------------
\* Participant Actions
\* ----------------------------------------------------------------------
SendVote(p) ==
    /\ Alive[p] = TRUE
    /\ RequestSent[p] = TRUE
    /\ SentVote[p] = FALSE
    /\ SentVote' = [SentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << Vote, Decision, Alive, Faulty,
                    RequestSent, ReceivedVote, BroadcastSent,
                    CoordDecision, CoordAlive, CoordFaulty,
                    BroadcastSent >>

AbortOnVote(p) ==
    /\ Alive[p] = TRUE
    /\ Decision[p] = undecided
    /\ SentVote[p] = TRUE
    /\ Vote[p] = no
    /\ Decision' = [Decision EXCEPT ![p] = abort]
    /\ UNCHANGED << Vote, SentVote, Alive, Faulty,
                    RequestSent, ReceivedVote, BroadcastSent,
                    CoordDecision, CoordAlive, CoordFaulty,
                    BroadcastSent >>

AbortOnTimeout(p) ==
    /\ Alive[p] = TRUE
    /\ Decision[p] = undecided
    /\ CoordAlive = FALSE
    /\ RequestSent[p] = FALSE
    /\ Decision' = [Decision EXCEPT ![p] = abort]
    /\ UNCHANGED << Vote, SentVote, Alive, Faulty,
                    RequestSent, ReceivedVote, BroadcastSent,
                    CoordDecision, CoordAlive, CoordFaulty,
                    BroadcastSent >>

DecideFromBroadcast(p) ==
    /\ Alive[p] = TRUE
    /\ Decision[p] = undecided
    /\ BroadcastSent[p] = TRUE
    /\ Decision' = [Decision EXCEPT ![p] = CoordDecision]
    /\ UNCHANGED << Vote, SentVote, Alive, Faulty,
                    RequestSent, ReceivedVote, BroadcastSent,
                    CoordDecision, CoordAlive, CoordFaulty >>

ParticipantDie(p) ==
    /\ Alive[p] = TRUE
    /\ Alive' = [Alive EXCEPT ![p] = FALSE]
    /\ Faulty' = [Faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << Vote, SentVote, Decision, RequestSent,
                    ReceivedVote, BroadcastSent,
                    CoordDecision, CoordAlive, CoordFaulty >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendReq(p)
    \/ \E p \in participants : RecvVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ MakeDecision
    \/ \E p \in participants : Broadcast(p)
    \/ CoordDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortOnVote(p)
    \/ \E p \in participants : AbortOnTimeout(p)
    \/ \E p \in participants : DecideFromBroadcast(p)
    \/ \E p \in participants : ParticipantDie(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type Invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ Vote \in [participants -> {yes, no}]
    /\ SentVote \in [participants -> BOOLEAN]
    /\ Decision \in [participants -> {undecided, commit, abort}]
    /\ Alive \in [participants -> BOOLEAN]
    /\ Faulty \in [participants -> BOOLEAN]
    /\ RequestSent \in [participants -> BOOLEAN]
    /\ ReceivedVote \in [participants -> {yes, no, waiting}]
    /\ BroadcastSent \in [participants -> BOOLEAN]
    /\ CoordDecision \in {undecided, commit, abort}
    /\ CoordAlive \in BOOLEAN
    /\ CoordFaulty \in BOOLEAN

====
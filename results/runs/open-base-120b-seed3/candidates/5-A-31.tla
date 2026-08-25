---- MODULE ACP_SB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* -------------------------------------------------
\* State Variables
\* -------------------------------------------------
VARIABLES
    vote,                \* [participants -> {yes,no}]
    sentVote,            \* [participants -> BOOLEAN]
    decision,            \* [participants -> {undecided,commit,abort}]
    requestSent,         \* [participants -> BOOLEAN]
    receivedVote,        \* [participants -> {yes,no,waiting}]
    broadcastSent,       \* [participants -> {commit,abort,notsent}]
    decisionCoord,       \* {undecided,commit,abort}
    coordAlive,          \* BOOLEAN
    coordFaulty,         \* BOOLEAN
    alive,               \* [participants -> BOOLEAN]
    faulty               \* [participants -> BOOLEAN]

\* -------------------------------------------------
\* Type Invariant
\* -------------------------------------------------
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ requestSent \in [participants -> BOOLEAN]
    /\ receivedVote \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \in [participants -> {commit, abort, notsent}]
    /\ decisionCoord \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ alive \in [participants -> BOOLEAN]
    /\ faulty \in [participants -> BOOLEAN]

\* -------------------------------------------------
\* Initial State
\* -------------------------------------------------
Init ==
    /\ vote \in [participants -> {yes, no}]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ decision = [p \in participants |-> undecided]
    /\ requestSent = [p \in participants |-> FALSE]
    /\ receivedVote = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]
    /\ decisionCoord = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ alive = [p \in participants |-> TRUE]
    /\ faulty = [p \in participants |-> FALSE]

\* -------------------------------------------------
\* Coordinator Actions
\* -------------------------------------------------
SendVoteReq(p) ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ ~requestSent[p]
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, sentVote, decision, receivedVote,
                    broadcastSent, decisionCoord,
                    coordAlive, coordFaulty, alive, faulty >>

ReceiveVote(p) ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ decisionCoord = undecided
    /\ requestSent[p]
    /\ receivedVote[p] = waiting
    /\ sentVote[p] = TRUE
    /\ receivedVote' = [receivedVote EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, sentVote, decision, requestSent,
                    broadcastSent, decisionCoord,
                    coordAlive, coordFaulty, alive, faulty >>

DetectFault(p) ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ decisionCoord = undecided
    /\ requestSent[p]
    /\ receivedVote[p] = waiting
    /\ faulty[p] = TRUE
    /\ decisionCoord' = abort
    /\ UNCHANGED << vote, sentVote, decision, requestSent,
                    receivedVote, broadcastSent,
                    coordAlive, coordFaulty, alive, faulty >>

MakeDecision ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ decisionCoord = undecided
    /\ \A p \in participants: receivedVote[p] # waiting
    /\ IF \A p \in participants: receivedVote[p] = yes
          THEN decisionCoord' = commit
          ELSE decisionCoord' = abort
    /\ UNCHANGED << vote, sentVote, decision, requestSent,
                    receivedVote, broadcastSent,
                    coordAlive, coordFaulty, alive, faulty >>

Broadcast(p) ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ decisionCoord # undecided
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = decisionCoord]
    /\ UNCHANGED << vote, sentVote, decision, requestSent,
                    receivedVote, decisionCoord,
                    coordAlive, coordFaulty, alive, faulty >>

DieCoord ==
    /\ coordAlive
    /\ ~coordFaulty
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED << vote, sentVote, decision, requestSent,
                    receivedVote, broadcastSent, decisionCoord,
                    alive, faulty >>

\* -------------------------------------------------
\* Participant Actions
\* -------------------------------------------------
SendVote(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ requestSent[p]
    /\ sentVote[p] = FALSE
    /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, decision, requestSent, receivedVote,
                    broadcastSent, decisionCoord,
                    coordAlive, coordFaulty, alive, faulty >>

AbortOnVote(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ decision[p] = undecided
    /\ sentVote[p] = TRUE
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, sentVote, requestSent, receivedVote,
                    broadcastSent, decisionCoord,
                    coordAlive, coordFaulty, alive, faulty >>

AbortOnTimeout(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ requestSent[p] = FALSE
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED << vote, sentVote, requestSent, receivedVote,
                    broadcastSent, decisionCoord,
                    coordAlive, coordFaulty, alive, faulty >>

AdoptDecision(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ decision[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED << vote, sentVote, requestSent, receivedVote,
                    broadcastSent, decisionCoord,
                    coordAlive, coordFaulty, alive, faulty >>

DieParticipant(p) ==
    /\ alive[p]
    /\ ~faulty[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, sentVote, decision, requestSent,
                    receivedVote, broadcastSent, decisionCoord,
                    coordAlive, coordFaulty >>

\* -------------------------------------------------
\* Action Aggregations
\* -------------------------------------------------
SendVoteReqAction == \E p \in participants: SendVoteReq(p)
ReceiveVoteAction == \E p \in participants: ReceiveVote(p)
DetectFaultAction == \E p \in participants: DetectFault(p)
BroadcastAction   == \E p \in participants: Broadcast(p)
SendVoteAction    == \E p \in participants: SendVote(p)
AbortOnVoteAction == \E p \in participants: AbortOnVote(p)
AbortOnTimeoutAction == \E p \in participants: AbortOnTimeout(p)
AdoptDecisionAction == \E p \in participants: AdoptDecision(p)
DieParticipantAction == \E p \in participants: DieParticipant(p)

CoordProgress == SendVoteReqAction \/ ReceiveVoteAction \/ DetectFaultAction \/ MakeDecision \/ BroadcastAction
PartProgress  == SendVoteAction \/ AbortOnVoteAction \/ AbortOnTimeoutAction \/ AdoptDecisionAction

Next == CoordProgress \/ PartProgress \/ DieCoord \/ DieParticipantAction

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<< vote, sentVote, decision, requestSent,
                              receivedVote, broadcastSent,
                              decisionCoord, coordAlive, coordFaulty,
                              alive, faulty >> 
                /\ WF(CoordProgress) 
                /\ WF(PartProgress)

\* -------------------------------------------------
\* Invariant
\* -------------------------------------------------
INVARIANT TypeInv

====
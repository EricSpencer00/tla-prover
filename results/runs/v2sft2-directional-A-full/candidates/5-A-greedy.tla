---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    vote,          \* [p \in participants |-> {yes, no}]
    alive,         \* [p \in participants \cup {coordinator} |-> BOOLEAN]
    finalDec,      \* [p \in participants |-> {undecided, commit, abort}]
    faulty,        \* [p \in participants \cup {coordinator} |-> BOOLEAN]
    sentVote,      \* [p \in participants |-> BOOLEAN]  \* whether p has sent its vote
    reqSent,       \* [p \in participants |-> BOOLEAN]  \* whether coordinator has sent vote request to p
    votesRecvd,    \* [p \in participants |-> {waiting, yes, no}]  \* coordinator's view of p's vote
    decision,      \* {undecided, commit, abort}  \* coordinator's decision
    broadcastSent  \* [p \in participants |-> BOOLEAN]  \* whether coordinator has broadcast its decision to p

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all actors (participants + coordinator)
Actors == participants \cup {coordinator}

\* The coordinator's name
coordinator == "coordinator"

\* The set of undecided participants
UndecidedP == {p \in participants : finalDec[p] = undecided}

\* The set of participants that have sent their vote
SentVoters == {p \in participants : sentVote[p]}

\* The set of participants that have received the coordinator's decision
DecidedP == {p \in participants : finalDec[p] \in {commit, abort}}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ vote = [p \in participants |-> CHOOSE v \in {yes, no} : v]
    /\ alive = [a \in Actors |-> TRUE]
    /\ finalDec = [p \in participants |-> undecided]
    /\ faulty = [a \in Actors |-> FALSE]
    /\ sentVote = [p \in participants |-> FALSE]
    /\ reqSent = [p \in participants |-> FALSE]
    /\ votesRecvd = [p \in participants |-> waiting]
    /\ decision = undecided
    /\ broadcastSent = [p \in participants |-> FALSE]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Coordinator sends a vote request to a participant
SendReq ==
    \E p \in participants :
        /\ alive[coordinator]
        /\ ~reqSent[p]
        /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED << vote, alive, finalDec, faulty, sentVote,
                       votesRecvd, decision, broadcastSent >>

\* Coordinator receives a vote from a participant
RecvVote ==
    \E p \in participants :
        /\ alive[coordinator]
        /\ decision = undecided
        /\ reqSent[p]
        /\ votesRecvd[p] = waiting
        /\ sentVote[p]
        /\ votesRecvd' = [votesRecvd EXCEPT ![p] = vote[p]]
        /\ UNCHANGED << vote, alive, finalDec, faulty, sentVote,
                       reqSent, decision, broadcastSent >>

\* Coordinator detects a participant fault (no vote sent)
DetectFault ==
    \E p \in participants :
        /\ alive[coordinator]
        /\ decision = undecided
        /\ reqSent[p]
        /\ votesRecvd[p] = waiting
        /\ ~sentVote[p]
        /\ faulty[p]
        /\ decision' = abort
        /\ UNCHANGED << vote, alive, finalDec, faulty, sentVote,
                       reqSent, votesRecvd, broadcastSent >>

\* Coordinator makes a decision after receiving all votes
MakeDecision ==
    /\ alive[coordinator]
    /\ decision = undecided
    /\ \A p \in participants : votesRecvd[p] \in {yes, no}
    /\ decision' = IF \A p \in participants : votesRecvd[p] = yes
                    THEN commit
                    ELSE abort
    /\ UNCHANGED << vote, alive, finalDec, faulty, sentVote,
                   reqSent, votesRecvd, broadcastSent >>

\* Coordinator broadcasts its decision to a participant
BroadcastDecision ==
    \E p \in participants :
        /\ alive[coordinator]
        /\ decision \in {commit, abort}
        /\ ~broadcastSent[p]
        /\ broadcastSent' = [broadcastSent EXCEPT ![p] = TRUE]
        /\ UNCHANGED << vote, alive, finalDec, faulty, sentVote,
                       reqSent, votesRecvd, decision >>

\* Coordinator dies
CoordDie ==
    /\ alive[coordinator]
    /\ alive' = [alive EXCEPT ![coordinator] = FALSE]
    /\ faulty' = [faulty EXCEPT ![coordinator] = TRUE]
    /\ UNCHANGED << vote, finalDec, sentVote, reqSent, votesRecvd,
                   decision, broadcastSent >>

\* Participant sends its vote (after receiving request)
SendVote ==
    \E p \in participants :
        /\ alive[p]
        /\ ~faulty[p]
        /\ reqSent[p]
        /\ ~sentVote[p]
        /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
        /\ UNCHANGED << vote, alive, finalDec, faulty, reqSent,
                       votesRecvd, decision, broadcastSent >>

\* Participant aborts unilaterally if its vote is no
AbortOnVote ==
    \E p \in participants :
        /\ alive[p]
        /\ ~faulty[p]
        /\ finalDec[p] = undecided
        /\ sentVote[p]
        /\ vote[p] = no
        /\ finalDec' = [finalDec EXCEPT ![p] = abort]
        /\ UNCHANGED << vote, alive, faulty, sentVote, reqSent,
                       votesRecvd, decision, broadcastSent >>

\* Participant aborts due to timeout (coordinator died without sending request)
AbortOnTimeout ==
    \E p \in participants :
        /\ alive[p]
        /\ ~faulty[p]
        /\ finalDec[p] = undecided
        /\ ~reqSent[p]
        /\ ~sentVote[p]
        /\ ~alive[coordinator]
        /\ finalDec' = [finalDec EXCEPT ![p] = abort]
        /\ UNCHANGED << vote, alive, faulty, sentVote, reqSent,
                       votesRecvd, decision, broadcastSent >>

\* Participant decides based on coordinator's broadcast
DecideFromBroadcast ==
    \E p \in participants :
        /\ alive[p]
        /\ ~faulty[p]
        /\ finalDec[p] = undecided
        /\ broadcastSent[p]
        /\ finalDec' = [finalDec EXCEPT ![p] = decision]
        /\ UNCHANGED << vote, alive, faulty, sentVote, reqSent,
                       votesRecvd, decision, broadcastSent >>

\* Participant dies
PartDie ==
    \E p \in participants :
        /\ alive[p]
        /\ alive' = [alive EXCEPT ![p] = FALSE]
        /\ faulty' = [faulty EXCEPT ![p] = TRUE]
        /\ UNCHANGED << vote, finalDec, sentVote, reqSent,
                       votesRecvd, decision, broadcastSent >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in participants : SendReq
    \/ \E p \in participants : RecvVote
    \/ \E p \in participants : DetectFault
    \/ MakeDecision
    \/ \E p \in participants : BroadcastDecision
    \/ CoordDie
    \/ \E p \in participants : SendVote
    \/ \E p \in participants : AbortOnVote
    \/ \E p \in participants : AbortOnTimeout
    \/ \E p \in participants : DecideFromBroadcast
    \/ \E p \in participants : PartDie

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<vote, alive, finalDec, faulty, sentVote,
                       reqSent, votesRecvd, decision, broadcastSent>>

\* ----------------------------------------------------------------------
\* Type invariant (for TLC)
\* ----------------------------------------------------------------------
TypeInv ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [Actors -> BOOLEAN]
    /\ finalDec \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [Actors -> BOOLEAN]
    /\ sentVote \in [participants -> BOOLEAN]
    /\ reqSent \in [participants -> BOOLEAN]
    /\ votesRecvd \in [participants -> {waiting, yes, no}]
    /\ decision \in {undecided, commit, abort}
    /\ broadcastSent \in [participants -> BOOLEAN]

====
---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

RECURSIVE VotedFor(_, _)
VotedFor(v, b) ==
    \/ \E a \in Acceptor : <<b, v>> \in votes[a]
    \/ \E c \in Ballot : c < b /\ VotedFor(v, c)

RECURSIVE Safe(_, _)
Safe(v, b) ==
    \A c \in Ballot : c < b => \E q \in Quorum :
        \A m \in q : (<<c, v>> \in votes[m]) \/ (\A a \in Acceptor : <<c, v>> \notin votes[a])

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

Promise(a, b) ==
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

CastVote(a, b, v) ==
    /\ b >= threshold[a]
    /\ ~\E w \in votes[a] : w[1] = b
    /\ \A a2 \in Acceptor : \A w \in votes[a2] : w[1] = b => w[2] = v
    /\ Safe(v, b)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

Chosen == { v \in Value : \E q \in Quorum : \A m \in q : <<1, v>> \in votes[m] }

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ threshold \in [Acceptor -> (-1) \cup Ballot]

OnlySafeVotes == \A a \in Acceptor : \A p \in votes[a] : Safe(p[2], p[1])

OneValuePerBallot == \A a1 \in Acceptor, a2 \in Acceptor :
    \A p1 \in votes[a1], p2 \in votes[a2] : (p1[1] = p2[1]) => (p1[2] = p2[2])

Inv == TypeOK /\ OnlySafeVotes /\ OneValuePerBallot

ConsensusSpecBar == Cardinality(Chosen) <= 1

====
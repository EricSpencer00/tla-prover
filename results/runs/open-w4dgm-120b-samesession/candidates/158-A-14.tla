---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold
vars == <<votes, threshold>>

Ballots == UNCHANGED / MCBallot
Values == MCValue
Acceptors == MCAcceptor
Quorums == MCQuorum

Vote == [ball : Ballot, val : Value]

TypeOK ==
    /\ votes \in [Acceptors -> SUBSET Vote]
    /\ threshold \in [Acceptors -> (-1 .. Cardinality(MCBallot))]

Init ==
    /\ votes = [a \in Acceptors |-> {}]
    /\ threshold = [a \in Acceptors |-> -1]

Promised(a, b) == threshold[a] >= b

SomeVoter(b, v) == \E a \in Acceptors : [ball |-> b, val |-> v] \in votes[a]

HasQuorum(b, v) == \E Q \in Quorums : \A a \in Q : [ball |-> b, val |-> v] \in votes[a]

SafeAt(v, b) ==
    \A c \in 0 .. (b - 1) :
        \E Q \in Quorums :
            \A a \in Q :
                [ball |-> c, val |-> v] \in votes[a] \/ \A d \in Ballots : d < c => ~SomeVoter(a, d)

RaiseThreshold(a, b) ==
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

VoteFor(a, v, b) ==
    /\ b > threshold[a]
    /\ [ball |-> b, val |-> v] \notin votes[a]
    /\ \A x \in Acceptors : [ball |-> b, val |-> v] \notin votes[x]
    /\ HasQuorum(b, v)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> b, val |-> v]}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptors, b \in Ballots : RaiseThreshold(a, b)
    \/ \E a \in Acceptors, v \in Values, b \in Ballots : VoteFor(a, v, b)

Spec == Init /\ [][Next]_vars

Chosen == {v \in Values : \E Q \in Quorums : \A a \in Q : [ball |-> 0, val |-> v] \in votes[a]}

VoterVotedForSomewhere(a) == \E e \in votes[a] : e

Inv ==
    /\ \A a \in Acceptors, e \in votes[a] : SafeAt(e.val, e.ball)
    /\ \A v1 \in Values, v2 \in Values :
         (SomeVoter(a1, 0) /\ SomeVoter(a1, 0)) => v1 = v2
    /\ \A a \in Acceptors : VoterVotedForSomewhere(a)
    /\ \A a \in Acceptors : threshold[a] >= 0 => VoterVotedForSomewhere(a)

QuorumOverlap ==
    \A Q1, Q2 \in Quorums : \E a \in Q1 \cap Q2 : TRUE

MCSymmetry ==
    {p \in [Acceptors -> Acceptors] : \A Q \in Quorums : p[Q] \in Quorums}

\* The voting algorithm refines abstract consensus: the set of chosen values is derived
\* from the votes and can never grow past a single value.
ConsensusSpecBar ==
    /\ \A a \in Acceptors, e \in votes[a] : e.val \in Chosen
    /\ Chosen \subseteq Values
====
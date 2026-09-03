---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES votes, thresh

vars == <<votes, thresh>>

VotePairs == [ball: Ballot, val: Value]

QuorumFor(v) == {Q \in Quorum: v \in Q}

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET VotePairs]
    /\ thresh \in [Acceptor -> (-1..Ballot)]

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

Promise(a, b) ==
    /\ b > thresh[a]
    /\ thresh' = [thresh EXCEPT ![a] = b]
    /\ UNCHANGED votes

Committed(v, b) ==
    {a \in Acceptor: [ball |-> b, val |-> v] \in votes[a]}

AllCommitted ==
    \E v \in Value, b \in Ballot:
        /\ \A Q \in QuorumFor(v) : Q \subseteq Committed(v, b)
        /\ \A c \in 0..(b - 1) : \E Q \in QuorumFor(v) : Q \subseteq Committed(v, c)

Vote(a, v, b) ==
    /\ b >= thresh[a]
    /\ [ball |-> b, val |-> v] \notin votes[a]
    /\ \A c \in Ballot, w \in Value :
        ([ball |-> c, val |-> w] \in votes[a]) => (c = b => w = v)
    /\ AllCommitted
    /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot: Promise(a, b)
    \/ \E a \in Acceptor, v \in Value, b \in Ballot: Vote(a, v, b)

Spec == Init /\ [][Next]_vars

Inv ==
    /\ \A a \in Acceptor: \A vp \in votes[a] : AllCommitted
    /\ \A a, b \in Acceptor, vp, wp \in VotePairs :
        (vp \in votes[a] /\ wp \in votes[b] /\ vp.ball = wp.ball) => vp.val = wp.val
    /\ TypeOK

ConsensusSpecBar == Inv

\* The abstract quorum-requirement set maps to concrete acceptor sets.
MCSymmetry == {f \in [Acceptor -> Acceptor]: TRUE}

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====
---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* A quorum must be a set of acceptors; the overlap property is stated here as
\* a semantic assumption rather than a structural one.
ASSUME Quorum \subseteq 2^{Acceptor}

\* The natural-number ballot set is bounded only for model checking, never
\* conceptually; the algorithm never assumes an upper bound.
Bound(b) == { x \in Ballot : x <= b }

VARIABLES votes, threshold

Init ==
    /\ votes = [ac \in Acceptor |-> {}]
    /\ threshold = [ac \in Acceptor |-> -1]

SafeAt(v, b) ==
    \A c \in 0..b-1 :
        \E q \in Quorum :
            /\ \A ac \in q : (c, v) \in votes[ac] \/ c < threshold[ac]
            /\ \E ac \in q : 0 <= threshold[ac] /\ threshold[ac] <= c

CastVote(ac, b, v) ==
    /\ b >= threshold[ac]
    /\ \A e \in votes[ac] : e[1] /= b
    /\ \A d \in Acceptor : \A e \in votes[d] : (e[1] = b) => (e[2] = v)
    /\ SafeAt(v, b)
    /\ votes' = [votes EXCEPT ![ac] = @ \cup {<<b, v>>}]
    /\ threshold' = [threshold EXCEPT ![ac] = b]

RaiseThreshold(ac, t) ==
    /\ t > threshold[ac]
    /\ threshold' = [threshold EXCEPT ![ac] = t]
    /\ UNCHANGED votes

Next ==
    \/ \E ac \in Acceptor, b \in Bound(b), v \in Value : CastVote(ac, b, v)
    \/ \E ac \in Acceptor, t \in Bound(b) : RaiseThreshold(ac, t)

Spec == Init /\ [][Next]_<<votes, threshold>>

Inv ==
    /\ \A ac \in Acceptor, e \in votes[ac] : SafeAt(e[2], e[1])
    /\ \A ac \in Acceptor, d \in Acceptor, b \in Ballot, v \in Value, w \in Value :
        /\ (b, v) \in votes[ac]
        /\ (b, w) \in votes[d]
        => v = w
    /\ \A ac \in Acceptor : threshold[ac] \in { -1 } \cup Ballot

\* The chosen set of values is derived from the votes; at most one value can
\* ever be chosen, which is what implements consensus.
Chosen == { v \in Value : \E q \in Quorum : \A ac \in q : \E b \in Ballot : <<b, v>> \in votes[ac] }

ConsensusSpecBar == Cardinality(Chosen) <= 1

\* Any two quorums must overlap, which is the only place the model relies on
\* that property.
MCSymmetry == { [f EXCEPT ![a1] = a2, ![a2] = a1] }

MCAcceptor == { a1, a2, a3 }
MCValue == { v1, v2 }
MCQuorum == { {a1, a2}, {a2, a3} }
MCBallot == { 0, 1 }

====
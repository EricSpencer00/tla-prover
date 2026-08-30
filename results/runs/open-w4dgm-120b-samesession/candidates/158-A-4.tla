---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == { {a1, a2}, {a2, a3}, {a1, a3} }
MCBallot == {0, 1}

VARIABLES votes, threshold

vars == <<votes, threshold>>

State == [ballot : Ballot, val : Value]
VotesFor(v, b) == {a \in Acceptor : [ballot |-> b, val |-> v] \in votes[a]}
Safe(v, b) ==
    \A c \in Ballot : c < b =>
        \E q \in Quorum :
            \A a \in q :
                (\A x \in votes[a] : x.ballot # c) \/ (\E x \in votes[a] : x.ballot = c /\ x.val = v)

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

RaiseThreshold(a, t) ==
    /\ t \notin threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = t]
    /\ UNCHANGED votes

Vote(a, v, b) ==
    /\ b >= threshold[a]
    /\ \A x \in votes[a] : x.ballot # b
    /\ \A c \in Ballot : c < b => \A q \in Quorum : \A a2 \in q : [ballot |-> c, val |-> v] \in votes[a2]
    /\ \A c \in Ballot : c < b => \E q \in Quorum : \A a2 \in q : [ballot |-> c, val |-> v] \in votes[a2]
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ballot |-> b, val |-> v]}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor : \E t \in MCBallot : RaiseThreshold(a, t)
    \/ \E a \in Acceptor : \E v \in MCValue : \E b \in MCBallot : Vote(a, v, b)

Spec == Init /\ [][Next]_vars

Inv ==
    /\ \A a \in Acceptor : \A x \in votes[a] : Safe(x.val, x.ballot)
    /\ \A a1 \in Acceptor : \A a2 \in Acceptor :
        \A x \in votes[a1] : \A y \in votes[a2] :
            (x.ballot = y.ballot) => (x.val = y.val)
    /\ \A a \in Acceptor : threshold[a] \in (-1) \cup MCBallot
    /\ \A a \in Acceptor : votes[a] \subseteq (MCBallot \X MCValue)

Chosen(v) == \E q \in Quorum : \A a \in q : [ballot |-> CHOOSE b \in Ballot : \E x \in votes[a] : x.ballot = b /\ x.val = v, val |-> v] \in votes[a]
ConsensusSpecBar == \A v \in MCValue : Chosen(v)

MCSymmetry == { p \in [A \in { {a1, a2}, {a2, a3}, {a1, a3} } |-> (A \cup {p[a1], p[a2], p[a3]})] : \E q \in Quorum : \E a2 \in q : p[a2] \in q }

====
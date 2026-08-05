---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

Vote == Ballot \X Value
Ax == {x[2] : x \in Vote}
Qm(p) == Cardinality({q \in Quorum : p \in q})
Safe(v, b) == \A c \in Ballot : (c < b) => (\E q \in Quorum : \A a \in q : (c, v) \in votes[a] \/ (b \notin {d[1] : d \in votes[a]}))

VARIABLES votes, thresh
vars == << votes, thresh >>

Init == /\ votes = [a \in Acceptor |-> {}]
        /\ thresh = [a \in Acceptor |-> -1]

CommitBallot(a) == {b \in Ballot : \E w \in Value : (b, w) \in votes[a]}
OtherVote(a, b) == \E a2 \in Acceptor : a2 # a /\ (b, votes[a][b]) \in votes[a2]

Promote(a, b) == /\ b > thresh[a]
                 /\ thresh' = [thresh EXCEPT ![a] = b]
                 /\ UNCHANGED votes
Vote(a, b, v) == /\ b >= thresh[a]
                 /\ (b, v) \notin votes[a]
                 /\ ~OtherVote(a, b)
                 /\ \E q \in Quorum : Qm(p) >= Cardinality(q) /\ \A x \in q : Safe(v, b)
                 /\ votes' = [votes EXCEPT ![a] = @ \cup {<< b, v >>}]
                 /\ thresh' = [thresh EXCEPT ![a] = b]

Next == \/ \E a \in Acceptor, b \in Ballot : Promote(a, b)
        \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

Inv == /\ (\A a \in Acceptor : \A x \in votes[a] : Safe(x[2], x[1]))
       /\ (\A a \in Acceptor : \A b \in Ballot : (b, votes[a][b]) \in votes[a] => \A a2 \in Acceptor : (b, votes[a2][b]) \in votes[a2] \/ votes[a2][b] = -1))
       /\ (\A a \in Acceptor : thresh[a] \in {-1} \cup Ballot)

ConsensusSpecBar == \A p \in Ax : Qm(p) >= 2 => \A q \in Quorum : p \in q

Permutation == [g \in [Acceptor -> Acceptor] | \A x, y \in Acceptor : (x # y => g[x] # g[y]) /\ (g[x] = x \/ g[x] = y \/ g[y] = y)]
MCSymmetry == {p \in Permutation : p = [x \in Acceptor |-> IF x = a1 THEN a2 ELSE IF x = a2 THEN a1 ELSE a3]}
MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {{a1, a2}, {a1, a3}, {a2, a3}}
MCBallot == {0, 1}
====
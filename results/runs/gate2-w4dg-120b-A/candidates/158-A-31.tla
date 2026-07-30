---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

\* An abstract consensus spec that the voting algorithm refines.
ConsensusSpecBar == Cardinality({\E q \in Quorum : \A a \in q : <<a, v>> \in votes}) <= 1

VARIABLES votes, threshold

vars == <<votes, threshold>>

\* A vote carries a ballot number and a value.  The threshold is the lowest
\* ballot an acceptor will still accept.
Vote == [ball : Ballot, val : Value]

Safe(v, b) ==
  /\ \A c \in 0..(b-1) : \E q \in Quorum :
        \A p \in q : (<<p, c, v>> \in votes) \/ \A d \in 0..(c-1) : <<p, d, v>> \notin votes

Init ==
  /\ votes = {}
  /\ threshold = [a \in Acceptor |-> -1]

Promote(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Vote(a, v, b) ==
  /\ b >= threshold[a]
  /\ ~(\E x \in votes : x.ball = b /\ x.val # v)
  /\ \A x \in votes : x.ball = b => x.val = v
  /\ Safe(v, b)
  /\ votes' = votes \cup {[ball |-> b, val |-> v, a |-> a]}
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promote(a, b)
  \/ \E a \in Acceptor, v \in Value, b \in Ballot : Vote(a, v, b)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A x \in votes : Safe(x.val, x.ball)
  /\ \A x, y \in votes : (x.ball = y.ball /\ x.val # y.val) => x.a = y.a
  /\ \A a \in Acceptor : threshold[a] \in (Ballot \cup {-1})

TypeOK ==
  /\ votes \subseteq [ball : Ballot, val : Value, a : Acceptor]
  /\ threshold \in [Acceptor -> (Ballot \cup {-1})]

====
---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {q1, q2, q3}
q1 == {a1, a2}
q2 == {a2, a3}
q3 == {a1, a3}
MCBallot == 0..2

VARIABLES votes, threshold
vars == <<votes, threshold>>

OVERLAP == \A a, b \in MCQuorum : a # b => (a \cap b) # {}

Vote == [ball : MCBallot, val : MCValue]
Cast == {x \in votes : TRUE}
Chosen == {x \in Cast : (\E q \in MCQuorum : \A a \in q : x \in votes[a])}

Safe == {x \in Vote : \A c \in 0..x.ball : \E q \in MCQuorum :
                     \A a \in q : (Vote \in votes[a] /\ votes[a].ball = c) \/ threshold[a] > c}

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ threshold = [a \in MCAcceptor |-> -1]

Raise(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Commit(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A c \in votes[a] : c.ball # b
  /\ (\A c \in Cast : c.ball = b => c.val = v)
  /\ (\E q \in MCQuorum : \A a' \in q :
        ([ball |-> b, val |-> v] \in votes[a'] \/ threshold[a'] > b))
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in MCAcceptor, b \in MCBallot : Raise(a, b)
  \/ \E a \in MCAcceptor, b \in MCBallot, v \in MCValue : Commit(a, b, v)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A a \in MCAcceptor : votes[a] \subseteq Vote
  /\ \A a \in MCAcceptor : \A v \in votes[a] : v \in Safe
  /\ \A a, b \in MCAcceptor, x \in votes[a], y \in votes[b] :
        (x.ball = y.ball) => (x.val = y.val)
  /\ \A a \in MCAcceptor : threshold[a] \in -1..MCBallot

ConsensusSpecBar == Cardinality(Chosen) <= 1
====
---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == << votes, threshold >>

VotePairs == [ballot : Ballot, val : Value]

Bump(b) == IF b = 0 THEN 0 ELSE b - 1

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

VoteSafe(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E q \in Quorum :
        \A a \in q :
          \A x \in VotePairs :
            /\ x \in votes[a]
            /\ x.ballot <= c
            => (x.val = v \/ x.ballot <= Bump(c))

VoteFor(a, v, b) ==
  /\ b >= threshold[a]
  /\ \A x \in votes[a] : x.ballot # b
  /\ \A x \in VotePairs : (x.val # v /\ x.ballot = b) \notin UNION {votes[a] : a \in Acceptor}
  /\ VoteSafe(v, b)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ballot |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

IncreaseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Next ==
  \/ \E a \in Acceptor, v \in Value, b \in Ballot : VoteFor(a, v, b)
  \/ \E a \in Acceptor, b \in Ballot : IncreaseThreshold(a, b)

Spec == Init /\ [][Next]_vars

Chosen ==
  { v \in Value : \E q \in Quorum : \A a \in q : \E x \in votes[a] : x.val = v }

Inv ==
  /\ \A a \in Acceptor : \A x \in votes[a] : VoteSafe(x.val, x.ballot)
  /\ \A x, y \in VotePairs : (x.val # y.val /\ x.ballot = y.ballot) => (x \notin UNION {votes[a] : a \in Acceptor})
  /\ \A a \in Acceptor : threshold[a] \in (-1)..Bump(^Ballot)

ConsensusSpecBar == Cardinality(Chosen) <= 1

====
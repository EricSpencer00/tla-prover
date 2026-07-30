---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS Acceptor, Value, Quorum, Ballot

ASSUME Quorum \subseteq SUBSET Acceptor

VARIABLES votes, threshold

vars == <<votes, threshold>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

QuorumSafe(v, b) ==
  \A c \in 0..(b - 1) : \E q \in Quorum :
    \A a \in q : (<<c, v>> \in votes[a]) \/ (\A v2 \in Value : <<c, v2>> \notin votes[a])

CastVote(a, v, b) ==
  /\ b >= threshold[a]
  /\ \A v2 \in Value : <<b, v2>> \notin votes[a]
  /\ \A a2 \in Acceptor : \A v2 \in Value :
       (<<b, v2>> \in votes[a2]) => (v2 = v)
  /\ QuorumSafe(v, b)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

RaiseThreshold(a, b) ==
  /\ b >= threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Next ==
  \/ \E a \in Acceptor : \E b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor : \E v \in Value : \E b \in Ballot : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

Chosen == {v \in Value :
  \E q \in Quorum : \A a \in q : \E b \in Ballot : <<b, v>> \in votes[a]}

Inv ==
  /\ \A a \in Acceptor : \A b \in Ballot : \A v \in Value : (<<b, v>> \in votes[a]) => QuorumSafe(v, b)
  /\ \A b \in Ballot :
       \A a1, a2 \in Acceptor : (\E v \in Value : <<b, v>> \in votes[a1]) /\ (\E v \in Value : <<b, v>> \in votes[a2])
         => (\A v \in Value : (<<b, v>> \in votes[a1]) <=> (<<b, v>> \in votes[a2]))
  /\ TypeOK

ConsensusSpecBar == Cardinality(Chosen) <= 1

====
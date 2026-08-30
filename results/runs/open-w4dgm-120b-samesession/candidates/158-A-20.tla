---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> (-1)..Ballot]

Quorums == (Quorum \ {{}}

VoteCount(v, b) == Cardinality({a \in Acceptor : <<b, v>> \in votes[a]})

Chosen == {v \in Value : \E b \in 1..Ballot : \E Q \in Quorums : \A a \in Q : <<b, v>> \in votes[a]}

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

NoVoteInBallot(b) == \A a \in Acceptor : <<b, v1>> \notin votes[a] /\ <<b, v2>> \notin votes[a]

Propose(a, b, v) ==
  /\ b >= threshold[a]
  /\ NoVoteInBallot(b)
  /\ \A c \in 1..(b - 1) : \E Q \in Quorums :
       \A a2 \in Q : <<c, v>> \in votes[a2] \/ (threshold[a2] >= c)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

RaiseThreshold(a, t) ==
  /\ t > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = t]
  /\ UNCHANGED votes

Next ==
  \/ \E a \in Acceptor, b \in 1..Ballot, v \in Value : Propose(a, b, v)
  \/ \E a \in Acceptor, t \in 1..Ballot : RaiseThreshold(a, t)

Spec == Init /\ [][Next]_vars

BallotSafe(b, v) ==
  \A c \in 1..(b - 1) : \E Q \in Quorums :
    \A a2 \in Q : <<c, v>> \in votes[a2] \/ (threshold[a2] >= c)

Inv ==
  /\ \A a \in Acceptor : \A p \in votes[a] : BallotSafe(p[1], p[2])
  /\ \A b \in 1..Ballot : \A v1, v2 \in Value :
       (NoVoteInBallot(b) \/ (\A a \in Acceptor : <<b, v1>> \in votes[a] => v1 = v2))
  /\ TypeOK

ConsensusSpecBar == ConsensusSpec == Chosen

MCSymmetry == {f \in [Acceptor -> Acceptor] : f \in Permutations(Acceptor)}
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot
====
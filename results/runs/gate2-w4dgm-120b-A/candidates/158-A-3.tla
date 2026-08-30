---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2

Acceptor == {a1, a2, a3}
Value == {v1, v2}
Quorum == {Q1, Q2}
Ballot == {0, 1}

VARIABLES votes, threshold
vars == <<votes, threshold>>

Vote == [ac : Acceptor, bal : Ballot, val : Value]

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumSet(f, S \ {x})

QuorumMemberCount(v, b) == SumSet([a \in Acceptor |-> IF [bal |-> b, val |-> v] \in votes[a] THEN 1 ELSE 0], Quorum)

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> {-1} \cup Ballot]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Agree(v, b) ==
  /\ \A a \in Acceptor : [bal |-> b, val |-> v] \notin votes[a]
  /\ \A c \in Ballot : \A w \in Value :
        (\A a \in Acceptor : [bal |-> c, val |-> w] \in votes[a]) => w = v

VotesAreSafe(v, b) ==
  /\ Agree(v, b)
  /\ \A c \in 0 .. (b - 1) :
       \E Q \in Quorum :
         \A a \in Q :
           ([bal |-> c, val |-> v] \in votes[a]) \/ (\A w \in Value : [bal |-> c, val |-> w] \notin votes[a])

CastVote(a, v, b) ==
  /\ threshold[a] <= b
  /\ [bal |-> b, val |-> v] \notin votes[a]
  /\ VotesAreSafe(v, b)
  /\ Cardinality({x \in Acceptor : [bal |-> b, val |-> v] \in votes[x]}) + 1 >= Cardinality(QuorumMemberCount(v, b)) + 1
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ac |-> a, bal |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, v \in Value, b \in Ballot : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ TypeOK
  /\ \A a \in Acceptor : \A c \in Ballot : \A w \in Value :
       ([bal |-> c, val |-> w] \in votes[a]) => VotesAreSafe(w, c)
  /\ \A v, w \in Value :
       ((\E a \in Acceptor : [bal |-> 0, val |-> v] \in votes[a]) /\ (\E a \in Acceptor : [bal |-> 0, val |-> w] \in votes[a]))
         => v = w
  /\ \A v, w \in Value : (\E a \in Acceptor : [bal |-> 1, val |-> v] \in votes[a]) /\ (\E a \in Acceptor : [bal |-> 1, val |-> w] \in votes[a]) => v = w

ConsensusSpecBar == Inv

Permutation == [a1 |-> a1, a2 |-> a2, a3 |-> a3]

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

MCSymmetry == {Permutation}
====
---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold
vars == <<votes, threshold>>

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

Vote == [ball : Ballot, val : Value]
QuorumIntersection == \A q1, q2 \in Quorum : q1 \cap q2 # {}

Chosen == {v \in Value : \E q \in Quorum : \A a \in q : <<1, v>> \in votes[a]}
SafeAt(v, b) == \A c \in 0 .. (b - 1) : \E q \in Quorum : \A a \in q : <<c, v>> \in votes[a] \/ threshold[a] > c

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> -1 .. (CHOOSE m \in Ballot : \A n \in Ballot : n <= m)]
  /\ QuorumIntersection

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

IncreaseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

CastVote(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A c \in votes[a] : c.ball < b
  /\ ~\E c \in votes[a] : c.ball = b
  /\ \A w \in Value : w # v => ~\E c \in votes[a] : c.ball = b /\ c.val = w
  /\ SafeAt(v, b)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor : \E b \in Ballot : IncreaseThreshold(a, b)
  \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ TypeOK
  /\ \A a \in Acceptor : \A e \in votes[a] : SafeAt(e.val, e.ball)
  /\ \A a, b \in Acceptor : \A e1 \in votes[a] : \A e2 \in votes[b] : e1.ball = e2.ball => e1.val = e2.val

ConsensusSpecBar == Spec /\ Inv
====
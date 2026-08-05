---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

VARIABLES votes, thresh

vars == <<votes, thresh>>

Vote == [ball : Ballot, val : Value]

Overlap == \A q1, q2 \in Quorum : q1 \cap q2 # {}

Safe(v, b) ==
  \A c \in Ballot :
    (c < b) => \E q \in Quorum : \A a \in q : ((c, v) \in votes[a] \/ c <= thresh[a])

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ thresh \in [Acceptor -> (Ballot \cup {-1})]
  /\ Quorum \subseteq SUBSET Acceptor

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

Promise ==
  /\ \E a \in Acceptor, b \in Ballot :
       /\ b > thresh[a]
       /\ thresh' = [thresh EXCEPT ![a] = b]
       /\ UNCHANGED votes

VoteCast ==
  /\ \E a \in Acceptor, b \in Ballot, v \in Value :
       /\ b >= thresh[a]
       /\ \A c \in Ballot : ((c, v) \in votes[a]) => c > b
       /\ \A c \in Ballot, w \in Value :
            ((c, w) \in votes[a]) => (c < b => w = v)
       /\ \E q \in Quorum : \A a2 \in q : Safe(v, b)
       /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
       /\ thresh' = [thresh EXCEPT ![a] = b]
  /\ UNCHANGED <<>>

Next == Promise \/ VoteCast

Spec == Init /\ [][Next]_vars

Chosen ==
  {v \in Value :
     \E b \in Ballot, q \in Quorum :
       \A a \in q : <<b, v>> \in votes[a]}

Inv ==
  /\ \A a \in Acceptor, x \in votes[a] : Safe(x.val, x.ball)
  /\ \A b \in Ballot : \A a1, a2 \in Acceptor :
       ((<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2)
  /\ TypeOK

ConsensusSpecBar == Cardinality(Chosen) <= 1

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

MCSymmetry ==
  {f \in [Acceptor -> Acceptor] : \A a \in Acceptor : f[a] = a}

====
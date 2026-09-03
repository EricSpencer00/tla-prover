---- MODULE Voting ----
EXTENDS Integers, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Vote == [ball : Ballot, val : Value]
Voters == [a1 |-> "a1", a2 |-> "a2", a3 |-> "a3"]
Quorums == {Q \in Quorum : Cardinality(Q) >= Cardinality(Acceptor) \div 2 + 1}

RECURSIVE SafeAt(_, _)
SafeAt(b, v) ==
  IF b = 0 THEN TRUE
  ELSE \E Q \in Quorums :
         \A a \in Q :
           \/ \E x \in {y \in Voters[a] : y.ball = b : x.val = v}
           \/ \A c \in 0..(b - 1) : ~(\E y \in Voters[a] : y.ball = c)

VARIABLES Voters, thresh
vars == <<Voters, thresh>>

CONSTANTS_None == -1

TypeOK ==
  /\ Voters \in [Acceptor -> SUBSET Vote]
  /\ thresh \in [Acceptor -> Ballot \cup {CONSTANTS_None}]

Init ==
  /\ Voters = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> CONSTANTS_None]

Promise(a, b) ==
  /\ (thresh[a] = CONSTANTS_None \/ b > thresh[a])
  /\ thresh' = [thresh EXCEPT ![a] = b]
  /\ UNCHANGED Voters

Vote(a, b, v) ==
  /\ (thresh[a] = CONSTANTS_None \/ b >= thresh[a])
  /\ \A x \in Voters[a] : x.ball # b
  /\ \A a2 \in Acceptor :
       \A x \in Voters[a2] : (x.ball = b /\ x.val # v) => FALSE
  /\ SafeAt(b, v)
  /\ Voters' = [Voters EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
  /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

Chosen(v) == \E Q \in Quorums : \A a \in Q : [ball |-> 0, val |-> v] \in Voters[a]

Inv ==
  /\ \A a \in Acceptor : \A x \in Voters[a] : SafeAt(x.ball, x.val)
  /\ (\A a, a2 \in Acceptor :
        \A x \in Voters[a] : \A y \in Voters[a2] :
          (x.ball = y.ball) => (x.val = y.val))
  /\ TypeOK

ConsensusSpecBar == \A v1, v2 \in Value : (Chosen(v1) /\ Chosen(v2)) => (v1 = v2)

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

MCSymmetry == (a1 :> a2 @@ a2 :> a1 @@ a3 :> a3)
====
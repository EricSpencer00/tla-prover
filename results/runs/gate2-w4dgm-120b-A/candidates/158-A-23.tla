---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

RECURSIVE SumFn(_, _)
SumFn(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumFn(f, S \ {x})

VARIABLES votes, thres

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ thres \in [Acceptor -> Ballot]

VoteSet == UNION {votes[a] : a \in Acceptor}

SafeAt(v, b) ==
  /\ <<b, v>> \in VoteSet
  /\ \A c \in Ballot :
       c < b => \E Q \in Quorum :
         \A a \in Q : (c \in thres[a] \/ <<c, v>> \in votes[a])

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thres = [a \in Acceptor |-> CHOOSE n \in Ballot : TRUE]

Promise(a, n) ==
  /\ n > thres[a]
  /\ thres' = [thres EXCEPT ![a] = n]
  /\ UNCHANGED votes

Vote(a, n, v) ==
  /\ n >= thres[a]
  /\ \A x \in votes[a] : x[1] # n
  /\ \A b \in Acceptor : <<n, v>> \notin votes[b]
  /\ \E Q \in Quorum : \A b \in Q : b = a \/ SafeAt(v, n)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<n, v>>}]
  /\ thres' = [thres EXCEPT ![a] = n]

Next ==
  \/ \E a \in Acceptor, n \in Ballot : Promise(a, n)
  \/ \E a \in Acceptor, n \in Ballot, v \in Value : Vote(a, n, v)

Spec == Init /\ [][Next]_<<votes, thres>>

Chosen == { v \in Value : \E b \in Ballot : <<b, v>> \in VoteSet }

Inv ==
  /\ \A v \in Value : SafeAt(v, 1)
  /\ \A a, b \in Acceptor :
       (\E n \in Ballot, v \in Value : <<n, v>> \in votes[a])
         => (\A n \in Ballot, v \in Value : <<n, v>> \in votes[b] => v = [n1 \in Ballot, v1 \in Value |-> <<n, v>>][a])
  /\ \A a \in Acceptor : votes[a] \subseteq Ballot \X Value
  /\ \A a \in Acceptor : thres[a] \in Ballot

ConsensusSpecBar == \A v \in Chosen : SafeAt(v, 1)

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

MCSymmetry == (a1 <-> a2 @@ a2 <-> a3 @@ a3 <-> a1)

====
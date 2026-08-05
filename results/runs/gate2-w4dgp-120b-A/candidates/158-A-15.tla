---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* Acceptor, Value, Quorum, and Ballot are declared as constants and instantiated
\* below with small finite sets (the MODEL section in the .cfg) for model checking.
\* The operators MCAcceptor, MCValue, MCQuorum, and MCBallot are the names the .cfg
\* substitutes in for those constants, so they must be defined here exactly as it
\* expects, matching the overloaded operators below.

CONSTANTS Acceptor, Value, Quorum, Ballot

VARIABLES casts, threshold

vars == <<casts, threshold>>

OVERLAP == \A q1 \in Quorum, q2 \in Quorum : q1 # q2 => (q1 \cap q2 # {})

Vote == [ball : Ballot, val : Value]
Chosen == {v \in Value : \E q \in Quorum : \A a \in q : <<a, v>> \in casts}
Meets(a, b, c) == \A q \in Quorum : \E a2 \in q : [ball |-> b, val |-> c] \in casts

\* A value is safe at ballot b if every lower ballot has a quorum endorsing it
\* (or players that can never vote in that ballot).
SafeAt(v, b) ==
  \A c \in Ballot : c < b =>
    \A q \in Quorum :
      \E a \in q : [ball |-> c, val |-> v] \in casts \/ threshold[a] > c

TypeOK == casts \subseteq [ball : Ballot, val : Value]
          /\ \A a \in Acceptor : threshold[a] \in Ballot \cup {-1}

Init ==
  casts = {} /\ threshold = [a \in Acceptor |-> -1]

Raise(a, b) ==
  LET nb == IF b > threshold[a] THEN b ELSE threshold[a] IN
    threshold' = [threshold EXCEPT ![a] = nb] /\ UNCHANGED casts

\* An acceptor votes for a value in a ballot, but only when no quorum has already
\* voted for a different value in that ballot.
Cast(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A c \in casts : c.ball = b => c.val = v
  /\ ~(\E c \in casts : c.ball = b /\ c.val # v)
  /\ SafeAt(v, b)
  /\ casts' = casts \cup {[ball |-> b, val |-> v]}
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \E a \in Acceptor :
    \E b \in Ballot :
      Raise(a, b) \/ (\E v \in Value : Cast(a, b, v))

Spec == Init /\ [][Next]_vars

Inv ==
  /\ TypeOK
  /\ \A c \in casts : SafeAt(c.val, c.ball)
  /\ \A c1, c2 \in casts : c1.ball = c2.ball => c1.val = c2.val

\* The voting algorithm implements consensus: the set of chosen values has size
\* at most one, so any two quorums that voted for a value must agree on it.
ConsensusSpecBar == Cardinality(Chosen) <= 1

MCSymmetry == {f \in [Acceptor -> Acceptor] : \A q \in Quorum : f[q] \in Quorum}

\* The overload is the identity on each of the constants.
Acceptor == MCAcceptor
Value == MCValue
Quorum == MCQuorum
Ballot == MCBallot

====
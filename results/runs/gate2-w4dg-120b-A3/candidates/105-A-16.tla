---- MODULE DyadicRationals ----
EXTENDS Integers

\* A dyadic rational is a pair of integers: a numerator and a denominator
\* that is a power of two. The state is a set of such pairs, always
\* containing the pair One = [num |-> 1, den |-> 1].
VARIABLES rs

TypeOK ==
  /\ rs \subseteq [num : Integers, den : Integers]
  /\ \A p \in rs : p.den > 0
  /\ \A p \in rs : p.den \in { 1, 2, 4, 8 }

Init ==
  /\ rs = { [num |-> 1, den |-> 1] }

\* Halve the denominator, leaving the value unchanged.
Halve(p) ==
  [num |-> p.num, den |-> p.den * 2]

\* Normalization only fires when both numerator and denominator are even.
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

One == [num |-> 1, den |-> 1]

Next ==
  \/ \E p \in rs : rs' = rs \cup { Halve(p) }
  \/ \E p \in rs :
       LET q == Norm([num |-> p.num \div 2, den |-> p.den \div 2])
       IN rs' = rs \cup { q }

Spec == Init /\ [][Next]_rs

RationalDenominatorIsPowerOfTwo ==
  \A p \in rs : p.den \in { 1, 2, 4, 8 }

NormalizationEventuallyHalts ==
  \A p \in rs : (p.num % 2 = 0 /\ p.den % 2 = 0) ~> (p.num % 2 # 0 \/ p.den % 2 # 0)

====
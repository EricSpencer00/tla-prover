---- MODULE DyadicRationals ----
EXTENDS Integers

\* Recursive normalization of dyadic rationals
RECURSIVE Norm(_)

\* The dyadic rational representing the value one
One == [num |-> 1, den |-> 1]

\* Halve a dyadic rational (multiply denominator by 2)
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Normalize by removing common factors of 2 from numerator and denominator
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p
====
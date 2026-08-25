---- MODULE DyadicRationals ----
EXTENDS Integers

\* Recursive definition of the normalization operator
RECURSIVE Norm(_)

\* The dyadic rational representing the value one
One == [num |-> 1, den |-> 1]

\* Halving a dyadic rational (multiply denominator by 2 and normalize)
Half(p) == Norm([num |-> p.num, den |-> p.den * 2])

\* Normalization: repeatedly divide numerator and denominator by 2 while both are even
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====
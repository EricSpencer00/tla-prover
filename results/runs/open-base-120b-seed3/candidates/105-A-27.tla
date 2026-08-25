---- MODULE DyadicRationals ----
EXTENDS Integers

\* Record type for dyadic rationals
Dyadic == [num : Int, den : Nat]

\* The dyadic rational representing the value one
One == [num |-> 1, den |-> 1]

\* Halving operator: multiplies denominator by two
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Recursive normalization: divide numerator and denominator by two
\* as long as both are even
RECURSIVE Norm(_)

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====
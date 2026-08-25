---- MODULE DyadicRationals ----
EXTENDS Integers

\* The dyadic rational representing the value one
One == [num |-> 1, den |-> 1]

\* Halving operator: multiplies the denominator by 2, leaving the numerator unchanged
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Normalization operator: repeatedly divides numerator and denominator by 2
\* as long as both are even.
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====
---- MODULE DyadicRationals ----
EXTENDS Integers

RECURSIVE Norm(_)

\* A dyadic rational is represented as a record with integer numerator and positive integer denominator
Dyadic == [num : Int, den : Nat]

\* The dyadic rational representing the value one
One == [num |-> 1, den |-> 1]

\* Halving operator: multiplies the denominator by 2, leaving the numerator unchanged
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Normalization operator: repeatedly divide numerator and denominator by 2 while both are even
Norm(p) == 
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====
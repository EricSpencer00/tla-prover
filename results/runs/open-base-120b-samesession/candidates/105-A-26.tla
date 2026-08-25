---- MODULE DyadicRationals ----
EXTENDS Integers

\* A dyadic rational is a record with integer numerator and positive integer denominator.
Dyadic == [num : Int, den : Nat]

\* The dyadic rational representing the value 1.
One == [num |-> 1, den |-> 1]

\* Halve a dyadic rational by doubling its denominator.
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Normalize a dyadic rational by repeatedly dividing numerator and denominator by 2
\* while both are even.
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====
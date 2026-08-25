---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Record type for dyadic rationals: numerator (integer) and denominator (natural)
\* ----------------------------------------------------------------------
Dyadic == [num : Int, den : Nat]

\* ----------------------------------------------------------------------
\* Constant representing the dyadic rational 1/1
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

\* ----------------------------------------------------------------------
\* Halving operator: multiplies the denominator by 2, leaving the numerator unchanged
\* ----------------------------------------------------------------------
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* ----------------------------------------------------------------------
\* Recursive normalization operator: repeatedly divides numerator and denominator
\* by 2 while both are even.
\* ----------------------------------------------------------------------
RECURSIVE Norm(_)

Norm(p) ==
  IF (p.num mod 2 = 0) /\ (p.den mod 2 = 0)
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====
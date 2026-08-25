---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLE p

\* Value representing the dyadic rational 1/1
One == [num |-> 1, den |-> 1]

\* Halving operator: doubles the denominator
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Normalization operator: repeatedly divide numerator and denominator by 2
RECURSIVE Norm(_)

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* Initial state: the rational 1
INIT == p = One

\* Next-state relation: either halve, normalize, or stay unchanged
NEXT ==
  \/ p' = Half(p)
  \/ p' = Norm(p)
  \/ p' = p

\* Full specification
SPECIFICATION == INIT /\ [][NEXT]_<<p>>

\* Simple invariant: denominator stays positive
INVARIANTS == p.den > 0

\* Trivial property (placeholder)
PROPERTIES == TRUE

====
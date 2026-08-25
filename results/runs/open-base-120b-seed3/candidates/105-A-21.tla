---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Dyadic rational numbers are represented as records with fields
\*   num : integer numerator
\*   den : integer denominator (always a positive power of two)
\* ----------------------------------------------------------------------

RECURSIVE Norm(_)

\* The dyadic rational representing the value one
One == [num |-> 1, den |-> 1]

\* Halving operator: divide the represented value by 2
Half(p) == Norm([num |-> p.num, den |-> p.den * 2])

\* Normalization: repeatedly divide numerator and denominator by 2
\* as long as both are even.
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====
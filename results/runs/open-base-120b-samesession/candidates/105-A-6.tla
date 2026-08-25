---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLES p

\* Constant representing the dyadic rational 1/1
One == [num |-> 1, den |-> 1]

\* Halving operator: doubles the denominator
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Normalization operator: repeatedly divide numerator and denominator by 2
RECURSIVE Norm(_)

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* Placeholder top‑level specifications required by the .cfg
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====
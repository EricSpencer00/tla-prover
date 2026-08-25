---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Record representing a dyadic rational: numerator (num) and denominator (den)
\* Both fields are integers, denominator is always positive after normalization.
\* ----------------------------------------------------------------------
VARIABLE p

\* ----------------------------------------------------------------------
\* Constants and Operators
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

Half(p) == Norm([num |-> p.num, den |-> p.den * 2])

RECURSIVE Norm(_)

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* ----------------------------------------------------------------------
\* Specification components required by the .cfg (even if empty)
\* ----------------------------------------------------------------------
INIT == p = One

NEXT == p' = Half(p)

SPECIFICATION == INIT /\ [][NEXT]_<<p>>

INVARIANTS == TRUE

PROPERTIES == TRUE

====
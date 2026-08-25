---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES dr

\* ----------------------------------------------------------------------
\* Type definition for dyadic rationals (record with fields num and den)
\* ----------------------------------------------------------------------
Dyadic == [num : Int, den : Int]

\* ----------------------------------------------------------------------
\* Constant dyadic rationals
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

\* ----------------------------------------------------------------------
\* Halving operator: multiplies the denominator by 2
\* ----------------------------------------------------------------------
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* ----------------------------------------------------------------------
\* Normalization operator: repeatedly divide numerator and denominator by 2
\* while both are even
\* ----------------------------------------------------------------------
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN
    Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE
    p

\* ----------------------------------------------------------------------
\* Specification (state machine)
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_<<dr>>

Init == dr = One

Next ==
  \/ dr' = Half(dr)
  \/ dr' = Norm(dr)

\* ----------------------------------------------------------------------
\* Invariant: numerator non‑negative, denominator positive and a power of two
\* ----------------------------------------------------------------------
IsPowerOfTwo(n) == n > 0 /\ \A k \in Nat : (2 ^ k = n) \/ (k = 0 /\ n = 1)

INVARIANTS == /\ dr.num >= 0
               /\ dr.den > 0
               /\ IsPowerOfTwo(dr.den)

\* ----------------------------------------------------------------------
\* Property (trivial example)
\* ----------------------------------------------------------------------
PROPERTIES == TRUE

====
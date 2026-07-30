---- MODULE DyadicRationals ----
EXTENDS Integers

\* Arithmetic on dyadic rationals, always normalized so that the numerator and
\* denominator are relatively prime (no factor of 2 is left over in both).
\* The configuration for this spec requires no extra constant declarations.
\* One and Half are the generating constants; Norm is the recursive
\* normalizer, and the spec explores the reachable states of its
\* initialization and halving.

CONSTANTS One, Half, Norm

VARIABLES p

vars == << p >>

Init == p = One

Step == p' = Norm([num |-> p.num, den |-> p.den * 2])

Next == Step

Spec == Init /\ [][Next]_vars

StateConstraint == p.den >= 1

NonzeroDenominator == p.den # 0

====
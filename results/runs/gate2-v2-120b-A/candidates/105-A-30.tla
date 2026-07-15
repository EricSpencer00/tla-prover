---- MODULE DyadicRationals ----
EXTENDS Integers, TLC

\* ----------------------------------------------------------------------
\* Constants (none required by the .cfg, but we declare the module name)
\* ----------------------------------------------------------------------
CONSTANTS

\* ----------------------------------------------------------------------
\* Record type for dyadic rationals
\* A dyadic rational is represented by a record with fields:
\*   num : Integer   \* numerator
\*   den : Integer   \* denominator (always > 0)
\* ----------------------------------------------------------------------
Rational == [num : Int, den : Nat \ {0}]

\* ----------------------------------------------------------------------
\* Initial state: the dyadic rational 1/1
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

\* ----------------------------------------------------------------------
\* Halving operator: multiply the denominator by 2, keep numerator
\* ----------------------------------------------------------------------
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* ----------------------------------------------------------------------
\* Normalization operator: while both numerator and denominator are even,
\* divide them by 2.  This implementation uses recursion with a well‑founded
\* measure based on the denominator.
\* ----------------------------------------------------------------------
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
VARIABLE x

\* Initial state: x is One
Init == x = One

\* Transition relation: either halve x, or normalize it.
Next ==
  \/ x' = Half(x)
  \/ x' = Norm(x)

\* Full specification (for model checking)
Spec == Init /\ [][Next]_<<x>>

\* ----------------------------------------------------------------------
\* Invariant: the value of x is always a dyadic rational with a positive
\* denominator.
\* ----------------------------------------------------------------------
IsDyadic(x) == x \in Rational

\* ----------------------------------------------------------------------
\* Optional properties (not required by the cfg but useful)
\* ----------------------------------------------------------------------
\* The value of x never changes its rational value when halved.
HalvePreservesValue ==
  \A p \in Rational : p.num / p.den = (Half(p)).num / (Half(p)).den

\* Normalization does not change the represented rational number.
NormPreservesValue ==
  \A p \in Rational : p.num / p.den = (Norm(p)).num / (Norm(p)).den

=============================================================================
---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Constants (no external constants required, but we expose the operators)
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Normalization: divide by 2 while both numerator and denominator are even
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* ----------------------------------------------------------------------
\* State variable: the current dyadic rational (record with fields num, den)
\* ----------------------------------------------------------------------
VARIABLE p

\* ----------------------------------------------------------------------
\* Initial state: start from the dyadic rational 1/1
\* ----------------------------------------------------------------------
Init == p = One

\* ----------------------------------------------------------------------
\* Next-state relation: nondeterministically either stay unchanged,
\* halve the rational, or normalize it.
\* ----------------------------------------------------------------------
Next ==
  \/ p' = p                                 \* stutter
  \/ p' = Half(p)                           \* halving step
  \/ p' = Norm(p)                           \* normalization step

\* ----------------------------------------------------------------------
\* Specification for TLC
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<p>>

\* ----------------------------------------------------------------------
\* Invariant: denominator is always positive and denominator is a power of two.
\* ----------------------------------------------------------------------
DenPos == p.den > 0

DenPowerOfTwo == \E n \in Nat : p.den = 2 ^ n

Inv == DenPos /\ DenPowerOfTwo

\* ----------------------------------------------------------------------
\* Property: the value represented by p is always a rational number
\* (i.e., numerator is an integer). This is trivially true but kept as an example.
\* ----------------------------------------------------------------------
ValueIsRational == p.num \in Int

=============================================================================
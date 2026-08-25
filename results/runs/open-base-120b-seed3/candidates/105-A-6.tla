---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Dyadic == [num : Int, den : Nat]

\* ----------------------------------------------------------------------
\* Constant dyadic rational representing one (1/1)
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

\* ----------------------------------------------------------------------
\* Halving operator: multiplies the denominator by 2, leaving the numerator
\* unchanged.
\* ----------------------------------------------------------------------
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* ----------------------------------------------------------------------
\* Normalisation operator: repeatedly divides numerator and denominator by 2
\* while both are even.
\* ----------------------------------------------------------------------
RECURSIVE Norm(_)

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

=============================================================================
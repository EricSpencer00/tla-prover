---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Dyadic rational numbers are represented as records with integer
\* numerator `num` and integer denominator `den`.  The denominator is
\* always a power of two after normalization.
\* ----------------------------------------------------------------------

\*--- Constants (none required)

\*--- Recursive definition of the normalization operator
RECURSIVE Norm

\*--- The dyadic rational representing the number one
One == [num |-> 1, den |-> 1]

\*--- Halving a dyadic rational (multiply denominator by 2)
Half(p) == [num |-> p.num, den |-> p.den * 2]

\*--- Normalization: repeatedly divide numerator and denominator by 2
\*    while both are even.
Norm(p) ==
  IF (p.num % 2 = 0) /\ (p.den % 2 = 0)
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\*--- (Optional) Predicate that a record is a dyadic rational
IsDyadic(p) == 
  /\ p \in [num : Int, den : Int]
  /\ p.den > 0
  /\ \E k \in Nat : p.den = 2^k

\*--- (Optional) The set of all dyadic rationals
Dyadic == { p : [num : Int, den : Int] : IsDyadic(p) }

====
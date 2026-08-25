---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Dyadic rational numbers are represented as records with fields
\*   num : integer numerator
\*   den : natural denominator that must be a power of two.
\* ----------------------------------------------------------------------

\* Helper predicate: a natural number is a power of two
IsPowerOfTwo(d) == 
    /\ d \in Nat
    /\ d > 0
    /\ \E n \in Nat : (2 ^ n) = d

\* The set of all dyadic rationals
Dyadic == { p \in [num : Int, den : Nat] : IsPowerOfTwo(p.den) }

\* The dyadic rational representing the value one
One == [num |-> 1, den |-> 1]

\* Halving operator: multiplies the denominator by 2 and then normalises
Half(p) == Norm([num |-> p.num, den |-> p.den * 2])

\* Recursive normalisation: repeatedly divide numerator and denominator by 2
\* as long as both are even.
RECURSIVE Norm(_)

Norm(p) == 
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

=============================================================================
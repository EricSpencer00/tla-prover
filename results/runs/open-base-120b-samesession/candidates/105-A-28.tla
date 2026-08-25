---- MODULE DyadicRationals ----
EXTENDS Integers, Naturals

\* ----------------------------------------------------------------------
\* Dyadic rational numbers are represented as records with integer numerator
\* and positive integer denominator that is a power of two.
\* ----------------------------------------------------------------------
Dyadic == { p \in [num : Int, den : Nat] :
               p.den > 0 /\ IsPowerOfTwo(p.den) }

IsPowerOfTwo(d) == \E n \in Nat : d = 2^n

\* ----------------------------------------------------------------------
\* Constant representing the dyadic rational 1/1
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

\* ----------------------------------------------------------------------
\* Halving operator: multiplies the denominator by 2 (leaves numerator unchanged)
\* ----------------------------------------------------------------------
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* ----------------------------------------------------------------------
\* Normalization operator: repeatedly divide numerator and denominator by 2
\* as long as both are even.
\* ----------------------------------------------------------------------
RECURSIVE Norm(_)

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====
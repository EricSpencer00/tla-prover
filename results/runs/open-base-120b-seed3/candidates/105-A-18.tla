---- MODULE DyadicRationals ----
EXTEND Integers

\* ----------------------------------------------------------------------
\* Dyadic rational numbers are represented as records with fields
\*   num : integer numerator
\*   den : integer denominator (must be > 0)
\* ----------------------------------------------------------------------
Dyadic == [num : Int, den : Int]

\* One = 1/1
One == [num |-> 1, den |-> 1]

\* Halving a dyadic rational: multiply the denominator by 2 and then
\* normalize the result.
Half(p) ==
    LET r == [num |-> p.num, den |-> p.den * 2] IN
    Norm(r)

\* Normalization: repeatedly divide numerator and denominator by 2
\* while both are even.
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====
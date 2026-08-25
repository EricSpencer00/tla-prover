---- MODULE DyadicRationals ----
EXTENDS Integers

\* Recursive normalization of a dyadic rational.
RECURSIVE Norm(_)

\* The dyadic rational representing the number one.
One == [num |-> 1, den |-> 1]

\* Halve a dyadic rational by doubling its denominator.
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Normalize by repeatedly dividing numerator and denominator by 2
\* while both are even.
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====
---- MODULE DyadicRationals ----
EXTENDS Integers

\* A dyadic rational is represented as a record with fields `num` (integer numerator)
\* and `den` (positive integer denominator).  No explicit type constraint is
\* required for the model; the operators enforce the intended structure.

One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p
====
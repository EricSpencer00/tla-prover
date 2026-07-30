---- MODULE DyadicRationals ----
EXTENDS Integers

\* A dyadic rational is a fraction with a power-of-two denominator.
\* We keep it as a record with a numerator and a denominator, and
\* the Norm operator keeps reducing the fraction by dividing both
\* parts by two whenever they are both even.

CONSTANTS One

VARIABLES val

TypeOK == val \in [num : Int, den : Int]

Init == val = One

\* Halve the denominator, leaving the value unchanged.
Halve == [num |-> val.num, den |-> val.den * 2]

\* Normalization: while both numerator and denominator are even, divide them by two.
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

Next == Halve \/ [val |-> Norm(val)]

Spec == Init /\ [][Next]_val

\* The fraction is never reduced to zero denominator.
DenNotZero == val.den # 0

\* The fraction is always an integer multiple of one over a power of two.
DyadicRational == val.num * 2 = val.den
====
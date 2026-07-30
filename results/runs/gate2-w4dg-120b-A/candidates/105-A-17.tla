---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

\* A dyadic rational is a fraction whose denominator is a power of two.  The
\* model normalizes such fractions by dividing out common factors of two.
\* (The spec mentions an IfThenElse clause; the two branches are the division
\* step and the base case where the fraction is already odd/even as required.)

VARIABLES p

vars == <<p>>

TypeOK ==
    /\ p \in [num : Int, den : (Nat \ {0})]

Init ==
    /\ p = [num |-> 1, den |-> 1]

Halve ==
    /\ p' = [num |-> p.num, den |-> p.den * 2]

NormStep ==
    /\ p.num % 2 = 0
    /\ p.den % 2 = 0
    /\ p' = [num |-> p.num \div 2, den |-> p.den \div 2]

Next ==
    \/ Halve
    \/ NormStep

Specification ==
    Init /\ [][Next]_vars

SpecHalt == TRUE

====
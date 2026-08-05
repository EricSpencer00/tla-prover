---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

Init ==
    /\ p = [num |-> 1, den |-> 1]

Halve ==
    /\ p' = [num |-> p.num, den |-> p.den * 2]

Normalize ==
    /\ IF p.num % 2 = 0 /\ p.den % 2 = 0
       THEN p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])
       ELSE p' = p

Next == Halve \/ Normalize

Spec == Init /\ [][Next]_vars

DenPositive == p.den > 0

====
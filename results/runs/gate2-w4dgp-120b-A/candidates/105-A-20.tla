---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

InitOne ==
    /\ p = One

HalfStep ==
    /\ p = Half
    /\ p' = Norm([num |-> p.num, den |-> p.den * 2])

NormStep ==
    /\ IF p.num % 2 = 0 /\ p.den % 2 = 0
       THEN p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])
       ELSE p' = p

Next == HalfStep \/ NormStep

Spec == InitOne /\ [][Next]_vars

====
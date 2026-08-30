---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

Init == p = One

Halve == p' = Half

Normalize == p' = Norm(p)

Next == Halve \/ Normalize

Spec == Init /\ [][Next]_vars

ValuesStayDyadic == p.den = 2 ^ (p.num - 1)

RationalIrrationality == p.num % p.den = p.num
====
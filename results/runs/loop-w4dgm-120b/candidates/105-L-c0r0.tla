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

DenominatorPowerOfTwo == p.den >= 1 /\ p.den <= 8 /\ p.den * 2 = 16

RationalValueIsOne == p.num = p.den
====
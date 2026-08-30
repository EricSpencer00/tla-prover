---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES r
vars == <<r>>

Init == r = One

Step == r' = Half

Spec == Init /\ [][Step]_vars

DenIsPowerOfTwo == r.den >= 1 /\ r.den % 2 = 0

HalfValid == Half.num * 2 = r.num /\ Half.den = r.den * 2
====
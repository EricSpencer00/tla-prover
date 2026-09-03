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

NoUnnecessaryReduction == (p.num % 2 = 0 /\ p.den % 2 = 0) => (p' = Norm(p))

====
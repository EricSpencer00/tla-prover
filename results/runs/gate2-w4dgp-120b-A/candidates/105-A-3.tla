---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm

VARIABLES p

vars == <<p>>

Init ==
    /\ p = One

Next ==
    \/ p' = Half[p]
    \/ p' = Norm[p]

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ p \in [num : INTEGER, den : INTEGER]
    /\ p.num >= 0
    /\ p.den >= 1

EvenProp == (p.num % 2 = 0 /\ p.den % 2 = 0) => (p.num % 2 = 0)

====
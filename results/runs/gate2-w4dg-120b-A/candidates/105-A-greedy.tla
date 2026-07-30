---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

TypeOK ==
    /\ p \in [num : 0..3, den : 1..4]

Init ==
    /\ p = One

Next ==
    /\ p' = Half

Spec ==
    /\ Init
    /\ [][Next]_vars

HalfSpec ==
    /\ p' = Half
    /\ UNCHANGED <<p>>

HalfInv ==
    /\ p.den \in {1, 2, 4}
    /\ p.num \in 0..3

HalfProp ==
    /\ p.den \in {1, 2, 4}
    /\ p.num \in 0..3

====
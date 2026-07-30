---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

TypeOK ==
    /\ p \in [num : 0 .. 3, den : 1 .. 4]

Init ==
    /\ p = One

Halt ==
    /\ p = Half

Halve ==
    /\ p # Half
    /\ p' = Half

Normalize ==
    /\ p # Half
    /\ ~(p.num % 2 = 0 /\ p.den % 2 = 0)
    /\ p' = Norm([num |-> p.num, den |-> p.den * 2])

Spec == Init /\ [][Halve \/ Normalize]_vars

StateConstraint ==
    /\ p.num \in 0 .. 3
    /\ p.den \in 1 .. 4

SpecHalt ==
    /\ (p = Half => [][Halt]_vars)
    /\ Spec

====
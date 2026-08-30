---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half

VARIABLES p

vars == <<p>>

TypeOK ==
    /\ p \in [ num : Int, den : Int ]

Init ==
    /\ p = One

Halve ==
    /\ p' = Half

Norm(q) ==
    IF q.num % 2 = 0 /\ q.den % 2 = 0
        THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
        ELSE q

Normalize ==
    /\ p' = Norm(p)

Spec ==
    /\ Init
    /\ [][Halve]_vars
    /\ [][Normalize]_vars

====
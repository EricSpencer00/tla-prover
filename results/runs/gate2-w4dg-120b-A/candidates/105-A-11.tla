---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half

VARIABLES p

vars == <<p>>

TypeOK ==
    /\ One \in [num : 1..2, den : 1..2]
    /\ Half \in [num : 0..2, den : 1..4]

Init ==
    /\ p = One

Next ==
    /\ p' = IF p.num % 2 = 0 /\ p.den % 2 = 0
            THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
            ELSE p

Spec ==
    /\ Init
    /\ [][Next]_vars

Norm(x) == [num |-> x.num % 2 + 2 * (x.num \div 2), den |-> x.den % 2 + 2 * (x.den \div 2)]

====
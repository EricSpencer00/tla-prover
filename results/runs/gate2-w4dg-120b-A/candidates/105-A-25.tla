---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

TypeOK == p \in [num : 1..4, den : 1..2]

Init == p = [num |-> 1, den |-> 1]

Specification == IF p.num % 2 = 0 /\ p.den % 2 = 0
                   THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
                   ELSE p

Next == p' = [num |-> p.num, den |-> p.den * 2]

Spec == Init /\ [][Specification]_p /\ [][Next]_p

Invariant == p.den # 0

SpecProp == p.den >= 1

====
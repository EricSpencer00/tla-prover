---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS Zero, One, Half

Dyadic == {p \in [num : Nat, den : {1, 2, 4}]}
Normalized == {p \in Dyadic : ~(p.num % 2 = 0 /\ p.den % 2 = 0)}

VARIABLES p

vars == <<p>>

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
             THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
             ELSE p

Init == p = [num |-> 1, den |-> 1]

Halve == p' = Norm([num |-> p.num, den |-> p.den * 2])

Next == Halve

Spec == Init /\ [][Next]_vars

TypeOK == p \in Dyadic

NormInv == p \in Normalized

====
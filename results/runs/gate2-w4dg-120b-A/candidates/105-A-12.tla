---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half

VARIABLES p

vars == <<p>>

RECURSIVE Norm(_)
Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0
            THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
            ELSE q

Init == p = One

Halve == p' = Half

TypeOK == p \in [num : Nat, den : Nat]

Spec == Init /\ [][Halve]_vars

====
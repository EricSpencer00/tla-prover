---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm

VARIABLES p

vars == <<p>>

Init == p = One

Next == p' = Half

TypeOK == p \in [num : Integer, den : Integer]

Spec == Init /\ [][Next]_vars

HalfDef == Half = [num |-> p.num, den |-> p.den * 2]

NormDef == Norm(p) = IF p.num % 2 = 0 /\ p.den % 2 = 0
                     THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
                     ELSE p

====
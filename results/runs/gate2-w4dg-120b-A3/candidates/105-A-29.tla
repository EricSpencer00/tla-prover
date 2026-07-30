---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

TypeOK == p \in [num : Int, den : Int]

Init == p = One

Next == \/ p' = Half
        \/ p' = IF p.num % 2 = 0 /\ p.den % 2 = 0
                THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
                ELSE p

Specification == Init /\ [][Next]_vars

InitInv == \A e \in {One, Half} : p = e

NormProp == (p.num % 2 = 0 /\ p.den % 2 = 0) ~> (p.den % 2 # 0 \/ p.num % 2 # 0)

====
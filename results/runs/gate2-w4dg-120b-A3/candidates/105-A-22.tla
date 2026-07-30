---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p
vars == <<p>>

TypeOK == p \in [num : Int, den : Int]

Init == p = One

Next == \/ p' = Half
        \/ p' = Norm(p)

Spec == Init /\ [][Next]_vars

One == [num |-> 1, den |-> 1]
Half == [num |-> p.num, den |-> p.den * 2]
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
           THEN [num |-> p.num \div 2, den |-> p.den \div 2]
           ELSE p
====
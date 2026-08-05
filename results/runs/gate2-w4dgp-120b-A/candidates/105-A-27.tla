---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANT Half

VARIABLES p

vars == <<p>>

One == [num |-> 1, den |-> 1]

Halve == [num |-> p.num, den |-> p.den * 2]

Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0 THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2]) ELSE q

Init == p = One

Next == p' \in {Halve, Norm(p), One}

Spec == Init /\ [][Next]_vars

====
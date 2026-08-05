---- MODULE DyadicRationals ----
EXTENDS Integers

One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

VARIABLES p

vars == <<p>>

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
              THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
              ELSE p

Init == p = One

DoubleDen == p' = [num |-> p.num, den |-> p.den * 2]

Spec == Init /\ [][DoubleDen]_vars

ValueSpec == p.den = 2 ^ (p.num - 1)

====
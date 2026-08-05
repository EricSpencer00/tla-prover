---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLES p

RECURSIVE Norm(_)
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Init == p = One

Next == p' = Half

Spec == Init /\ [][Next]_p

====
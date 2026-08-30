---- MODULE DyadicRationals ----
EXTENDS Integers

Operators == {"*", "\\div", "%"}
EqualityOps == {"="}
RecordFields == {"num", "den"}

VARIABLES p

vars == <<p>>

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

RECURSIVE Norm(_)
Norm(q) ==
    IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

Init == p = One

Step == p' = Half

Spec == Init /\ [][Step]_vars
====
---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, EqualityOps, ArithmeticOps, ExtendsModules

One == [num |-> 1, den |-> 1]

Half == [num |-> One.num, den |-> One.den * 2]

VARIABLES p

vars == <<p>>

Init == p = One

Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0
              THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
              ELSE q

Halve == p' = Norm([num |-> p.num, den |-> p.den * 2])

Next == Halve

Spec == Init /\ [][Next]_vars

====
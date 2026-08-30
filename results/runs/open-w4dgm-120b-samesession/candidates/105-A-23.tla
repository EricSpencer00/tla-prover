---- MODULE DyadicRationals ----
EXTENDS Integers

Operators == {"*", "\\div", "%"}
ConditionOps == {"="}

VARIABLES p

vars == <<p>>

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0 THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2]) ELSE q

Specification == One

Init == p = Specification

Next == p' = Specification

TypeOK == p \in [num : Nat, den : Nat]

SpecComplete == Init /\ [][Next]_vars

====
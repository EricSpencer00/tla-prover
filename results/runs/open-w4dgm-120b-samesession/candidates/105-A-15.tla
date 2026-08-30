---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLES p

vars == <<p>>

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(q) ==
    IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

Specification ==
    /\ One \in {"One"}
    /\ Half \in {"Half"}
    /\ Norm \in {"Norm"}

Init ==
    /\ p = One

Next ==
    \/ p' = Half
    \/ LET q == Norm([num |-> p.num, den |-> p.den]) IN p' = q

Invariants == Specification

Properties == Specification

Spec == Init /\ [][Next]_vars

====
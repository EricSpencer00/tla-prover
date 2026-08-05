---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS m, n

VARIABLES p

vars == <<p>>

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0
              THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
              ELSE q

Init == p = One

Step == p' = Norm(Half)

Spec == Init /\ [][Step]_vars

TypeOK == \A x \in {m, n} : p.x \in Nat /\ p.den \in Nat

Prop == p.num <= p.den

====
---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS num, den

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

Next == p' = Half

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ p \in [num : Int, den : Int]

NormFixedPoint ==
  /\ \A q \in [num : Int, den : Int] : Norm(q) = q

====
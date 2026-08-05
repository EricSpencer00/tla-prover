---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS
  One, Half, Norm

VARIABLES p

vars == <<p>>

Init ==
  /\ p = [num |-> 1, den |-> 1]

NormStep(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0 THEN [num |-> q.num \div 2, den |-> q.den \div 2] ELSE q

Next ==
  \/ p' = [num |-> p.num, den |-> p.den * 2]
  \/ p' = NormStep(p)

Spec == Init /\ [][Next]_p

NormRec ==
  /\ p = [num |-> 1, den |-> 1]
  /\ \A q \in [num : Integer, den : Integer] : (q.num % 2 = 0 /\ q.den % 2 = 0) ~> (q.num % 2 # 0 \/ q.den % 2 # 0)

====
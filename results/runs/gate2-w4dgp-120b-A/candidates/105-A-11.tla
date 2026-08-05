---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS MaxDen

VARIABLES p

vars == <<p>>

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0 THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2]) ELSE q

Init == p = One

Halve == p' = [num |-> p.num, den |-> p.den * 2]

Reduce == p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])

Next == Halve \/ Reduce

Spec == Init /\ [][Next]_vars

DenBound == p.den <= MaxDen

NormFixed == Norm(p) = p

====
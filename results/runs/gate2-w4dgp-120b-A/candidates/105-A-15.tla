---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

RECURSIVE Norm(_)

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
              THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
              ELSE p

VARIABLES r

vars == <<r>>

Init == r = [num |-> 1, den |-> 1]

HalfStep == r' = [num |-> r.num, den |-> r.den * 2]

NormStep == r' = Norm(r)

Next == HalfStep \/ NormStep

Spec == Init /\ [][Next]_vars

====
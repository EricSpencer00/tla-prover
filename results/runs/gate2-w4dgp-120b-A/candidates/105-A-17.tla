---- MODULE DyadicRationals ----
EXTENDS Integers

One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

Variables v

Init == v = One

ApplyHalf == v' = Norm([num |-> v.num, den |-> v.den * 2])

Spec == Init /\ [][ApplyHalf]_v

====
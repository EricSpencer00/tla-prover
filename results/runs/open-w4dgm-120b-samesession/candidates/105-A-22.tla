---- MODULE DyadicRationals ----
CONSTANTS Integers

VARIABLES p

TypeOK == p \in [num : Integers, den : Integers]

Init == p = [num |-> 1, den |-> 1]

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0 THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2]) ELSE q

Next == p' = One \/ p' = Half \/ p' = Norm(p)

Spec == Init /\ [][Next]_p

DenomPowerOfTwo == \E n \in Nat : p.den = 1 << n

DenomPositive == p.den > 0

====
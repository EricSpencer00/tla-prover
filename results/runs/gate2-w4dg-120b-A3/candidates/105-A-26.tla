---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half

VARIABLES p

vars == <<p>>

TypeOK == p \in [num : Nat, den : Nat]

Init == p = One

Next == p' = Half \/ p' = Norm([num |-> p.num, den |-> p.den * 2])

Spec == Init /\ [][Next]_vars

Even == p.num % 2 = 0 /\ p.den % 2 = 0

Norm(r) == IF r.num % 2 = 0 /\ r.den % 2 = 0
             THEN Norm([num |-> r.num \div 2, den |-> r.den \div 2])
             ELSE r

InvariantP == p.num >= 0 /\ p.den > 0

SpecSet == {Spec}

====
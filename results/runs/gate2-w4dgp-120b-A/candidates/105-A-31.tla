---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS MaxNum, MaxDen

Zero == [num |-> 0, den |-> 1]
One == [num |-> 1, den |-> 1]

VARIABLES p, q

vars == <<p, q>>

Norm(x) ==
    IF x.num % 2 = 0 /\ x.den % 2 = 0
    THEN Norm([num |-> x.num \div 2, den |-> x.den \div 2])
    ELSE x

TypeOK ==
    /\ p.num \in 1..MaxNum /\ p.den \in 1..MaxDen
    /\ q.num \in 1..MaxNum /\ q.den \in 1..MaxDen

Init ==
    /\ p = One
    /\ q = Zero

Halve ==
    /\ q' = Norm([num |-> p.num, den |-> p.den * 2])
    /\ UNCHANGED p

Recurse ==
    /\ p' = Norm([num |-> p.num, den |-> p.den * 2])
    /\ UNCHANGED q

Next == Halve \/ Recurse

Spec == Init /\ [][Next]_vars

TypeOKInv == TypeOK

====
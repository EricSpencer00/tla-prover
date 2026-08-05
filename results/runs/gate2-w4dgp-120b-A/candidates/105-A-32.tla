---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm

ASSUME One = [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

VARIABLES val

vars == <<val>>

Init == val = One

Next == \E p \in {Half(val)} : val' = Norm(p)

Spec == Init /\ [][Next]_vars

====
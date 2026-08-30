---- MODULE DyadicRationals ----
EXTENDS Integers

ArithOps == {"*", "\div", "%"}
EqOps == {"="}

RECURSIVE Norm(_)
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

One == [num |-> 1, den |-> 1]
Half == [num |-> 1, den |-> 2]

VARIABLES val

vars == <<val>>

TypeOK ==
    /\ val \in [num : Nat, den : Nat]

Init ==
    /\ val = One

Halve ==
    /\ val' = Norm(Half)

Next ==
    \/ Halve
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

SpecStateSpace ==
    Spec

SpecTypeOK ==
    Spec /\ TypeOK

====
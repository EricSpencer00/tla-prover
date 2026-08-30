---- MODULE DyadicRationals ----
EXTENDS Integers

ArithOps == {"*", "\div", "%"}
EqualityOps == {"="}

One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

VARIABLES val

vars == <<val>>

Init ==
    /\ val = One

Halve ==
    /\ val' = [num |-> val.num, den |-> val.den * 2]

Reduce ==
    /\ val' = Norm(val)

Next ==
    \/ Halve
    \/ Reduce

Spec == Init /\ [][Next]_vars

ValueIsDyadic == val.den > 0 /\ \A i \in 1..val.den : val.den % i = 0 => i = 1

ValueWithinBounds ==
    /\ val.den >= 1
    /\ val.den <= 16
    /\ val.num >= 0
    /\ val.num <= 16

====
---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

Init ==
    /\ p = [num |-> 1, den |-> 1]

Halve ==
    /\ p' = [num |-> p.num, den |-> p.den * 2]
    /\ UNCHANGED One
    /\ UNCHANGED Half
    /\ UNCHANGED Norm

NormStep ==
    /\ p.num % 2 = 0 /\ p.den % 2 = 0
    /\ p' = [num |-> p.num \div 2, den |-> p.den \div 2]
    /\ UNCHANGED One
    /\ UNCHANGED Half
    /\ UNCHANGED Norm

Next ==
    \/ Halve
    \/ NormStep

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ p \in [num : Int, den : Int]
    /\ One = [num |-> 1, den |-> 1]
    /\ Half = [num |-> 1, den |-> 2]

NormalizationHalt ==
    (p.num % 2 = 0 /\ p.den % 2 = 0) ~> (p.num % 2 # 0 \/ p.den % 2 # 0)

====
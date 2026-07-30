---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

TypeOK ==
    /\ p \in [num : (Nat \ {0}), den : (Nat \ {0})]
    /\ One \in [num : Nat, den : Nat]
    /\ Half \in [num : Nat, den : Nat]

Init ==
    /\ p = [num |-> 1, den |-> 1]
    /\ One = [num |-> 1, den |-> 1]
    /\ Half = [num |-> 1, den |-> 2]

NormRec ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN NormRec
    ELSE p

Norm == NormRec

Halve ==
    /\ p' = [num |-> p.num, den |-> p.den * 2]
    /\ UNCHANGED <<One, Half>>

Specification == Init /\ [][Halve]_vars

NormSpec == Norm

====
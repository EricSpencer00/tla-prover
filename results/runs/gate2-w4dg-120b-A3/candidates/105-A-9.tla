---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS
    One
    Half
    Norm

VARIABLES
    p

vars == <<p>>

TypeOK ==
    /\ p \in [num : Nat, den : Nat]
    /\ One \in [num : Nat, den : Nat]
    /\ Half \in [num : Nat, den : Nat]
    /\ Norm \in [num : Nat, den : Nat] => [num : Nat, den : Nat]

Init ==
    /\ p = [num |-> 1, den |-> 1]
    /\ One = [num |-> 1, den |-> 1]
    /\ Half = [num |-> 1, den |-> 2]

NormRec(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN NormRec([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

Next ==
    \/ p' = [num |-> p.num, den |-> p.den * 2]
    \/ p' = NormRec([num |-> p.num \div 2, den |-> p.den \div 2])
    /\ UNCHANGED <<One, Half, Norm>>

Spec == Init /\ [][Next]_vars

====
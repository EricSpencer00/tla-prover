---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS Norm, Half, One

VARIABLES r

vars == <<r>>

TypeOK ==
    /\ r \in [num : Nat, den : Nat]
    /\ Norm \in [num : Nat, den : Nat]
    /\ Half \in [num : Nat, den : Nat]
    /\ One \in [num : Nat, den : Nat]

InitAccident == [num |-> 3, den |-> 2]

Init ==
    /\ r = InitAccident
    /\ Norm = [num |-> 1, den |-> 1]
    /\ Half = [num |-> 1, den |-> 2]
    /\ One = [num |-> 1, den |-> 1]

NormStep(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

HalfRec(p) == NormStep([num |-> p.num, den |-> p.den * 2])

Next ==
    /\ r' = HalfRec(r)
    /\ UNCHANGED <<Norm, Half, One>>

Spec == Init /\ [][Next]_vars

InitOnly == Spec /\ UNCHANGED vars

HalfInv == r.den \in {1, 2}

HalfPreservesDen == (r.den = 1) ~> (r.den \in {1, 2})

====
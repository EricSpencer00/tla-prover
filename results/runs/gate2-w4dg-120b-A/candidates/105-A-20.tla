---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm

VARIABLES p

vars == <<p>>

TypeOK ==
    /\ p \in [num : Int, den : Int]

Init ==
    /\ p = One

Next ==
    /\ p' = Half

Spec ==
    /\ Init
    /\ [][Next]_vars

Halve ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

OneDef ==
    One = [num |-> 1, den |-> 1]

HalfDef ==
    Half = [num |-> p.num, den |-> p.den * 2]

NormDef ==
    Norm(r) ==
        IF r.num % 2 = 0 /\ r.den % 2 = 0
        THEN Norm([num |-> r.num \div 2, den |-> r.den \div 2])
        ELSE r

====
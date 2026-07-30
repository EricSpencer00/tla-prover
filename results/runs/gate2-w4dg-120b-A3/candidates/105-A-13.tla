---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

TypeOK ==
    /\ p \in [num : 0 .. 7, den : 1 .. 8]
    /\ One \in [num : 0 .. 7, den : 1 .. 8]
    /\ Half \in [num : 0 .. 7, den : 1 .. 8]
    /\ Norm \in [num : 0 .. 7, den : 1 .. 8]

Init ==
    /\ p = [num |-> 1, den |-> 1]
    /\ One = [num |-> 1, den |-> 1]
    /\ Half = [num |-> 1, den |-> 2]

Specification ==
    /\ TypeOK
    /\ Init
    /\ Next

Next ==
    \/ \E p' == [num |-> p.num, den |-> p.den * 2] : p' # p /\ p' # [num |-> 0, den |-> 1]
    \/ \E p' == IF p.num % 2 = 0 /\ p.den % 2 = 0
                THEN [num |-> p.num \div 2, den |-> p.den \div 2]
                ELSE p : p' # p

====
---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

Spec == One /\ [num |-> 1, den |-> 1]
Half == [num |-> p.num, den |-> p.den * 2]
Norm == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN [num |-> p.num \div 2, den |-> p.den \div 2] ELSE p

Init == p = [num |-> 1, den |-> 1]

Next == p' = IF p.den % 2 = 0 THEN [num |-> p.num, den |-> p.den * 2] ELSE p

Spec == Init
====
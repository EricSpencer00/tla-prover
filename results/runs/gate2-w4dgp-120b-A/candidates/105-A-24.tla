---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS one, half, norm

RECURSIVE Norm(_)
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

VARIABLES r
vars == <<r>>

Spec == r' = one

Init == r = one

NextStep == r' = half /\ r.num % 2 = 0

Inv == norm /\ r.den >= 2

====
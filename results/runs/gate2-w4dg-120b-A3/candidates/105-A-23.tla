---- MODULE DyadicRationals ----
EXTENDS Naturals

CONSTANTS One, Half

RECURSIVE Norm(_)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

VARIABLES num, den

vars == <<num, den>>

TypeOK ==
    /\ num \in Nat
    /\ den \in Nat

Init ==
    /\ num = One.num
    /\ den = One.den

Spec ==
    \/ Init
    \/ [vars EXCEPT !.num = den, !.den = num * 2]

HalfSpec ==
    /\ num' = Half.num
    /\ den' = Half.den
    /\ UNCHANGED <<num, den>>

SpecAll == Spec \/ HalfSpec

SpecInit == Spec

====
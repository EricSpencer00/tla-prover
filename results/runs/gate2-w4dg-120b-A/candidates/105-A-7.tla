---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p
vars == <<p>>

TypeOK == p \in [num : Nat, den : Nat]

Init ==
    /\ p \in {One, Half}
    /\ p.den # 0

Next ==
    \/ \E q \in {One, Half} : p' = q
    \/ p' = Norm([num |-> p.num, den |-> p.den * 2])
    \/ p' = IF p.num % 2 = 0 /\ p.den % 2 = 0
              THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
              ELSE p

Spec == Init /\ [][Next]_vars

DenominatorBound == p.den <= 8

HalfIsHalfOfOne == Half.den = 2 * One.den
====
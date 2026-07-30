---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

Init == \E q \in {[num |-> 1, den |-> 1]}
          /\ p = q

Next == \E q \in {[num |-> p.num, den |-> p.den * 2]}
          /\ p' = q
        \/ /\ p.num % 2 = 0
           /\ p.den % 2 = 0
           /\ p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])
        \/ p' = p

Spec == Init /\ [][Next]_vars

CONSTANTS dx == 1
CONSTANTS dy == 1
CONSTANTS dz == 1

TypeOK == p \in [num : Integers, den : Integers]

StateConstraint == p.num \in Nat /\ p.den \in Nat /\ p.den # 0

SpecConstr == Spec /\ TypeOK /\ StateConstraint

HalfIsNeverZero == Half # 0

InitDoublesDen == p.den = 2 * dy

====
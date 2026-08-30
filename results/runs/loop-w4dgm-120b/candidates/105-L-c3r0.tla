---- MODULE DyadicRationals ----
EXTENDS Integers

RECURSIVE Norm(_)
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
             THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
             ELSE p

One == [num |-> 1, den |-> 1]

Half == [num |-> One.num, den |-> One.den * 2]

VARIABLES state

vars == <<state>>

Init == state = One

HalfStep == state' = [num |-> state.num, den |-> state.den * 2]

Normalize == state' = Norm(state)

Next == HalfStep \/ Normalize

Spec == Init /\ [][Next]_vars

DenominatorPositive == state.den > 0

ValueWithinUnitInterval == state.num >= 0 /\ state.num <= state.den

====
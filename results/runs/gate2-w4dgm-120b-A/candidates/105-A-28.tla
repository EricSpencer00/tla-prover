---- MODULE DyadicRationals ----
EXTENDS Integers

One == [num |-> 1, den |-> 1]

Half == [num |-> One.num, den |-> One.den * 2]

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
              THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
              ELSE p

VARIABLES state

vars == <<state>>

Init == state = One

Double == state' = [num |-> state.num, den |-> state.den * 2]

Halve == state' = Half

Normalize == state' = Norm(state)

Next == Double \/ Halve \/ Normalize

Spec == Init /\ [][Next]_vars

Rational == state.num % state.den = state.num

DenominatorIsPowerOfTwo == \A k \in Nat : state.den = 2 ^ k

====
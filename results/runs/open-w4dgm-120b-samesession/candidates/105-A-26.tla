---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithOps

One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

RECURSIVE Norm(_)
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
              THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
              ELSE p

VARIABLES current
vars == <<current>>

Init == current = One

Halve == current' = Norm([num |-> current.num, den |-> current.den * 2])

Next == Halve

Specification == Init /\ [][Next]_vars

ArithInv == current.num >= 0 /\ current.den > 0

RationalCoherence == current.num % 2 = 1 \/ current.den = 1

SpecProperties == RationalCoherence

TypeOK == current \in [num : Nat, den : Nat]
====
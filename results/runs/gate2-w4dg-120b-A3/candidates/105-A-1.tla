---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm

VARIABLES p

vars == <<p>>

Init == p = [num |-> 1, den |-> 1]

HalfOp == p' = [num |-> p.num, den |-> p.den * 2]

NormRec ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
  THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

Next == HalfOp \/ (\E q \in [num : INTEGER, den : INTEGER] : q = NormRec /\ p' = q)

Specification == Init /\ [][Next]_vars

InitInv == p.den = 1 \/ p.den = 2

NormInv == p.den = 2 => p.num % 2 = 1

TypeOK == p \in [num : INTEGER, den : {1, 2}]

====
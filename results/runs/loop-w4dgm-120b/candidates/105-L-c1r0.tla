---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

ASSUME One = [num |-> 1, den |-> 1]
ASSUME Half = [num |-> 1, den |-> 2]

VARIABLES p

vars == <<p>>

Init == p = One

NormStep ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
  THEN [num |-> p.num \div 2, den |-> p.den \div 2]
  ELSE p

Specification == Init /\ [][~>]_vars

TypeOK == p \in {[num : Nat, den : Nat]}

StateConstraint == p.num <= 2 /\ p.den <= 4

====
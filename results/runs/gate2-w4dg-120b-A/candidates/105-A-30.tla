---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm

VARIABLES p

vars == <<p>>

TypeOK ==
  /\ p \in [num : Int, den : Int]
  /\ p.den >= 1
  /\ p.den <= 8
  /\ p.num >= 0
  /\ p.num <= 8

Init ==
  /\ p = [num |-> 1, den |-> 1]

Specification ==
  /\ p' = [num |-> p.num, den |-> p.den * 2]

Halve ==
  /\ p' = [num |-> p.num, den |-> p.den * 2]

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
  THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

Next ==
  \/ Specification
  \/ Halve

Spec == Init /\ [][Next]_vars

Invariant ==
  /\ p.den >= 1
  /\ p.den <= 8
  /\ p.num >= 0
  /\ p.num <= 8
  /\ (p.den % 2 = 0 /\ p.num % 2 = 1) \/ (p.den % 2 = 1)

Property ==
  p.den % 2 = 1

====
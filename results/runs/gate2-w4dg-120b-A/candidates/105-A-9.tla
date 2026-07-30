---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm

RECURSIVE Specification(_)
Specification(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
  THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

RECURSIVE Init(_)
Init(_)= [num |-> 1, den |-> 1]

RECURSIVE Next(_)
Next(_)= [num |-> p.num, den |-> p.den * 2]

RECURSIVE Invariants(_)
Invariants(_)= [num |-> p.num, den |-> p.den]

RECURSIVE Properties(_)
Properties(_)= [num |-> p.num, den |-> p.den]

====
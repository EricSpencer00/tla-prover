---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS
  One
  Half
  Norm

ASSUME One = [num |-> 1, den |-> 1]
ASSUME Half = [num |-> 1, den |-> 2]

VARIABLES p

vars == <<p>>

TypeOK ==
  /\ p \in [num : Integers, den : Integers]
  /\ p.den > 0
  /\ p.num >= 0

Init ==
  /\ p = One

Specification ==
  /\ p.num * Half.den = Half.num * p.den
  /\ IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p' = p
  /\ UNCHANGED <<One, Half>>

Next ==
  \/ /\ p = One
     /\ p' = Half
     /\ UNCHANGED <<One, Half>>
  \/ /\ p # One
     /\ p' = Half
     /\ UNCHANGED <<One, Half>>

Spec == Specification

====
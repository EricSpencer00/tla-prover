---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm
CONSTANTS Specification
CONSTANTS INIT
CONSTANTS NEXT
CONSTANTS INVARIANTS
CONSTANTS PROPERTIES

VARIABLES p

vars == p

TypeOK ==
  /\ p \in [num : Nat, den : Nat]

Init ==
  /\ p = [num |-> 1, den |-> 1]

Specification ==
  /\ (p # One) \/ (p # Half) \/ (p # Norm([num |-> p.num \div 2, den |-> p.den \div 2]))

Next ==
  \/ IF p = One
       THEN p' = [num |-> 2, den |-> 1]
     ELSE IF p = Half
       THEN p' = [num |-> 1, den |-> 2]
     ELSE p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  /\ UNCHANGED <<One, Half, Norm, Specification, INIT, NEXT, INVARIANTS, PROPERTIES>>

Spec == Init /\ [][Next]_vars

INVARIANTS == {}
PROPERTIES == {}
====
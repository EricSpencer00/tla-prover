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
    /\ p \in [num : INTEGER, den : INTEGER]

Init ==
    /\ p = [num |-> 1, den |-> 1]

Next ==
    /\ \/ p' = [num |-> p.num, den |-> p.den * 2]
       \/ IF p.num % 2 = 0 /\ p.den % 2 = 0
          THEN p' = [num |-> p.num \div 2, den |-> p.den \div 2]
          ELSE p' = p
    /\ UNCHANGED <<One, Half, Norm, Specification, INIT, NEXT, INVARIANTS, PROPERTIES>>

Specification == Init /\ [][Next]_vars
INVARIANTS == TypeOK
PROPERTIES == TRUE
====
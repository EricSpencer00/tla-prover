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

vars == <<p>>

TypeOK ==
    /\ p \in [num : 0 .. 3, den : 1 .. 3]

Init ==
    /\ p = [num |-> 1, den |-> 1]
    /\ One = [num |-> 1, den |-> 1]

Halve ==
    /\ p' = [num |-> p.num, den |-> p.den * 2]
    /\ UNCHANGED <<One, Half, Norm, Specification, INIT, NEXT, INVARIANTS, PROPERTIES>>

Recurs ==
    /\ p' = IF p.num % 2 = 0 /\ p.den % 2 = 0
            THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
            ELSE p
    /\ UNCHANGED <<One, Half, Norm, Specification, INIT, NEXT, INVARIANTS, PROPERTIES>>

Next ==
    \/ Halve
    \/ Recurs

Spec ==
    /\ Init /\ [][Next]_vars
    /\ Specification = Spec
    /\ UNCHANGED <<One, Half, Norm, INIT, NEXT, INVARIANTS, PROPERTIES>>

====
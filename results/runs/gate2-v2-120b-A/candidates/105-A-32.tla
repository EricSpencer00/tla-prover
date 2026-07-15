---- MODULE DyadicRationals ----
EXTENDS Integers, Sequences, TLC

\* ----------------------------------------------------------------------
\* Identifiers required by the description
\* ----------------------------------------------------------------------
CONSTANTS
    One,        \* dyadic rational representing 1
    Half,       \* dyadic rational representing 1/2
    Norm        \* normalization operator (function)

\* ----------------------------------------------------------------------
\* Record type for dyadic rationals
\* ----------------------------------------------------------------------
Dyadic == [num : Int, den : Nat]

\* ----------------------------------------------------------------------
\* Helper definitions for the constants
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]
Half == [num |-> 1, den |-> 2]

\* ----------------------------------------------------------------------
\* Normalization operator: reduces a dyadic rational while both parts are even
\* ----------------------------------------------------------------------
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
        THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
        ELSE p

\* ----------------------------------------------------------------------
\* The set of all dyadic rationals (denominator is a positive power of two)
\* ----------------------------------------------------------------------
DyadicSet == { p : Dyadic :
                p.den > 0 /\ \A i \in 1..p.den : i \in Nat => i = 1 \/ i % 2 = 0
                /\ p = Norm(p) }

\* ----------------------------------------------------------------------
\* STATE VARIABLE
\* ----------------------------------------------------------------------
VARIABLE cur

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Init ==
    /\ cur = One
    /\ cur \in DyadicSet

Next ==
    \/ /\ cur' = Half
       /\ cur' \in DyadicSet
    \/ /\ cur' = Norm([num |-> cur.num, den |-> cur.den * 2])
       /\ cur' \in DyadicSet

Spec == Init /\ [][Next]_<<cur>>

\* ----------------------------------------------------------------------
\* Invariants and properties required by the reference .cfg (none)
\* ----------------------------------------------------------------------
\* (The .cfg does not request any specific invariant or property,
\*  but we include a generic type invariant for completeness.)

Inv ==
    cur \in DyadicSet

=============================================================================
---- MODULE DyadicRationals ----
EXTENDS Integers, TLC

\* ----------------------------------------------------------------------
\* Constants (none required by the .cfg, but we keep the list for clarity)
\* ----------------------------------------------------------------------
CONSTANTS

\* ----------------------------------------------------------------------
\* Value One: the dyadic rational representing the integer 1
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

\* ----------------------------------------------------------------------
\* Halving operator: given a dyadic rational p, produce a dyadic rational
\*   with the same numerator and double the denominator.
\* ----------------------------------------------------------------------
Half(p) == [num |-> p["num"], den |-> p["den"] * 2]

\* ----------------------------------------------------------------------
\* Normalization operator: repeatedly divide numerator and denominator by 2
\* while both are even.  This implements the description:
\*   IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN
\*       Norm([num |-> p.num \div 2, den |-> p.den \div 2])
\*   ELSE p
\* ----------------------------------------------------------------------
RECURSIVE Norm(_)
Norm(p) ==
    IF (p["num"] % 2 = 0) /\ (p["den"] % 2 = 0) THEN
        Norm([num |-> p["num"] \div 2,
              den |-> p["den"] \div 2])
    ELSE p

\* ----------------------------------------------------------------------
\* Type invariant: each dyadic rational has a positive denominator.
\* ----------------------------------------------------------------------
TypeInv == \A p \in Dyadics : p["den"] > 0

\* ----------------------------------------------------------------------
\* The set of all dyadic rationals (used for state variables and quantification)
\* ----------------------------------------------------------------------
Dyadics == { [num |-> n, den |-> d] : n \in Int, d \in Nat \ {0} }

\* ----------------------------------------------------------------------
\* State variable representing the current dyadic rational
\* ----------------------------------------------------------------------
VARIABLES p

\* ----------------------------------------------------------------------
\* Initialization: start with the value One, normalized (which is just One)
\* ----------------------------------------------------------------------
Init == p = Norm(One)

\* ----------------------------------------------------------------------
\* Next-state relation:
\*   - Halve: replace p by Half(p) and then normalize.
\*   - DoNothing: stay in the same state.
\* ----------------------------------------------------------------------
Next ==
    \/ p' = Norm(Half(p))
    \/ p' = p

\* ----------------------------------------------------------------------
\* Specification (the main temporal formula)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<p>>

\* ----------------------------------------------------------------------
\* The .cfg does not require explicit names for SPECIFICATION, INIT,
\* NEXT, INVARIANTS, or PROPERTIES, but we expose them with the exact
\* identifiers requested.
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == TypeInv
PROPERTIES == {}

=============================================================================
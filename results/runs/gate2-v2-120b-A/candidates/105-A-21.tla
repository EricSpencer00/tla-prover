---- MODULE DyadicRationals ----
EXTENDS Integers, Sequences

\* ----------------------------------------------------------------------
\* Constants (none required by the .cfg, but we keep this section for
\* completeness; they could be instantiated in the .cfg if desired)
\* ----------------------------------------------------------------------
CONSTANTS

\* ----------------------------------------------------------------------
\* State variables
\*   p   : the current dyadic rational, represented as a record
\*         with fields 'num' (numerator) and 'den' (denominator)
\* ----------------------------------------------------------------------
VARIABLES p

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

\* Recursive normalization: repeatedly divides numerator and denominator
\* by 2 while both are even.  The recursion stops when at least one of the
\* two numbers is odd.
Norm(r) ==
    IF r.num % 2 = 0 /\ r.den % 2 = 0
        THEN Norm([num |-> r.num \div 2, den |-> r.den \div 2])
        ELSE r

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ p = One

\* ----------------------------------------------------------------------
\* Next-state relation
\*   The system may either halve the current dyadic rational, or
\*   apply a single step of the normalization process.
\* ----------------------------------------------------------------------
Next ==
    \/ /\ p' = Half
    \/ /\ p' = IF p.num % 2 = 0 /\ p.den % 2 = 0
                THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
                ELSE p

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<p>>

\* ----------------------------------------------------------------------
\* Invariants
\*   PositiveDenominator ensures the denominator never becomes zero
\*   NormalizedInvariant states that the state is either already
\*   normalized or can be normalized by applying Norm once.
\* ----------------------------------------------------------------------
PositiveDenominator ==
    p.den > 0

NormalizedInvariant ==
    /\ p.den > 0
    /\ (p.num % 2 # 0 \/ p.den % 2 # 0)   \* at least one of numerator/denominator is odd

\* ----------------------------------------------------------------------
\* The set of all reachable states (useful for debugging, not exported)
\* ----------------------------------------------------------------------
Reachable ==
    { p : <>_<<p>> Spec }

\* ----------------------------------------------------------------------
\* The specification's name for TLC
\* ----------------------------------------------------------------------
SPECIFICATION Spec
INVARIANTS PositiveDenominator, NormalizedInvariant

====
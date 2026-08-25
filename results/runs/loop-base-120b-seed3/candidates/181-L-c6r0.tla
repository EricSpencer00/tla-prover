---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers used for model checking.
\* ----------------------------------------------------------------------
NatOverride == 0..MaxNat

VARIABLE n

\* ----------------------------------------------------------------------
\* Initial state: n ranges over the finite natural numbers.
\* ----------------------------------------------------------------------
Init ==
    /\ n \in NatOverride

\* ----------------------------------------------------------------------
\* Next-state relation: n steps to any (finite) natural number.
\* ----------------------------------------------------------------------
Next ==
    /\ n' \in NatOverride
    /\ n' = n + 1

\* ----------------------------------------------------------------------
\* Specification required by the configuration.
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_<<n>>

\* ----------------------------------------------------------------------
\* Names required by the .cfg file.
\* ----------------------------------------------------------------------
INIT == Init
NEXT == Next

Even(x) == x % 2 = 0

INVARIANTS == \A m \in NatOverride : Even(2 * m)

PROPERTIES == INVARIANTS
====
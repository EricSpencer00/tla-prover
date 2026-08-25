---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers used for model checking.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

VARIABLES n

\* ----------------------------------------------------------------------
\* Initial state: n ranges over the finite natural numbers.
\* ----------------------------------------------------------------------
Init ==
    /\ n \in NatOverride

\* ----------------------------------------------------------------------
\* Next-state relation: n steps to the next natural number (if within bound).
\* ----------------------------------------------------------------------
Next ==
    /\ n' = n + 1
    /\ n' \in NatOverride

\* ----------------------------------------------------------------------
\* Specification required by the configuration.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<n>>

\* ----------------------------------------------------------------------
\* Names required by the .cfg file.
\* ----------------------------------------------------------------------
\* (The .cfg file expects Init and Next directly; no additional alias needed.)

Even(x) == x % 2 = 0

INVARIANTS == \A m \in NatOverride : Even(2 * m)

PROPERTIES == INVARIANTS
====
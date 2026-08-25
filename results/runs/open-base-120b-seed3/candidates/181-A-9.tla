---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers for model checking.
\* The .cfg file replaces Nat with NatOverride, so we provide the finite set.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Simple state variable used to illustrate the theorem.
\* ----------------------------------------------------------------------
VARIABLE n

\* ----------------------------------------------------------------------
\* Predicate stating that a number is even.
\* ----------------------------------------------------------------------
IsEven(m) == m % 2 = 0

\* ----------------------------------------------------------------------
\* Initial state: n ranges over the finite natural numbers.
\* ----------------------------------------------------------------------
Init == n \in NatOverride

\* ----------------------------------------------------------------------
\* Next-state relation: n may take any value in the finite range.
\* ----------------------------------------------------------------------
Next == n' \in NatOverride

\* ----------------------------------------------------------------------
\* Full specification of the system.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<n>>

\* ----------------------------------------------------------------------
\* Identifiers required by the .cfg file.
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == IsEven(2 * n)
PROPERTIES == INVARIANTS

====
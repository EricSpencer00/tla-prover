---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers

CONSTANT MaxNat

\* ----------------------------------------------------------------------
\* Finite version of Nat for model checking (overridden in the .cfg file)
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

VARIABLE n

\* ----------------------------------------------------------------------
\* Initial predicate: n can take any value in the finite range.
\* This definition will be used as the initial state predicate by TLC.
\* ----------------------------------------------------------------------
Init == n \in NatOverride

\* ----------------------------------------------------------------------
\* Next-state relation: nondeterministically assign a new value to n
\* within the same finite range.
\* ----------------------------------------------------------------------
Next == n' \in NatOverride

\* ----------------------------------------------------------------------
\* Overall specification (convenient for manual reasoning)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<n>>

\* ----------------------------------------------------------------------
\* Invariant: the double of any natural number in the finite range is even.
\* ----------------------------------------------------------------------
Inv == \A m \in NatOverride : (2 * m) % 2 = 0

\* ----------------------------------------------------------------------
\* Property to be checked by TLC.
\* ----------------------------------------------------------------------
Properties == []Inv
====
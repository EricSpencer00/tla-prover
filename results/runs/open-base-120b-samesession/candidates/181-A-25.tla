---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial predicate
INIT == n \in NatOverride

\* Next-state relation (allows any value in the finite range)
NEXT == n' \in NatOverride

\* Specification combining init and next
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* Helper predicate: evenness
IsEven(m) == m % 2 = 0

\* Invariant expressing that double of any number is even
INVARIANTS == IsEven(2 * n)

\* Property (same as the invariant for this simple model)
PROPERTIES == IsEven(2 * n)
====
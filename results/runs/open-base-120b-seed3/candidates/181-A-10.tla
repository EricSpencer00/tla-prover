---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLES n

\* Helper definition: a number is even iff its remainder modulo 2 is 0
IsEven(m) == m % 2 = 0

\* Initial predicate
INIT == n \in NatOverride

\* Next-state relation (nondeterministically picks any natural in the finite range)
NEXT == n' \in NatOverride

\* Main specification
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* Invariant stating that double of any n is even
INVARIANTS == IsEven(2 * n)

\* Property to be checked (same as the invariant)
PROPERTIES == INVARIANTS
====================================================
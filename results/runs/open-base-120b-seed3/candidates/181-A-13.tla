---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

VARIABLE n

\* Finite version of the natural numbers up to MaxNat
NatOverride == 0 .. MaxNat

\* Predicate defining even numbers (using the finite NatOverride for witnesses)
IsEven(m) == \E k \in NatOverride : m = 2 * k

\* Initial state: start with the smallest natural number
INIT == n \in NatOverride /\ n = 0

\* Next-state relation: nondeterministically choose any natural number in the finite range
NEXT == n' \in NatOverride

\* Full specification for TLC
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* Invariant stating that the double of any natural number in the range is even
INVARIANTS == \A m \in NatOverride : IsEven(2 * m)

\* Property (the same as the invariant) for model checking
PROPERTIES == INVARIANTS

====
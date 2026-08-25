---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: n ranges over the finite natural numbers
INIT == n \in NatOverride

\* Next-state relation: nondeterministically choose any value in NatOverride
NEXT == n' \in NatOverride

\* Full specification
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* Predicate defining even numbers (within the finite range)
IsEven(m) == (\E k \in NatOverride : m = 2 * k)

\* Theorem: double of any natural number is even (assumed for checking)
THEOREM == \A x \in NatOverride : IsEven(2 * x)

\* Invariants and properties to be checked
INVARIANTS == THEOREM
PROPERTIES == THEOREM
====
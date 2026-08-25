---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

VARIABLES n

\* Finite version of the natural numbers used by the model checker.
NatOverride == 0 .. MaxNat

\* Theorem: the double of any natural number is even.
DoubleEven == \A m \in NatOverride: (2 * m) % 2 = 0

\* Initial state: start with zero.
INIT == n = 0

\* Next-state relation: n can take any value in the finite natural range.
NEXT == n' \in NatOverride

\* Overall specification.
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* Invariant(s) to be checked.
INVARIANTS == DoubleEven

\* Additional properties (here the same theorem).
PROPERTIES == DoubleEven
====
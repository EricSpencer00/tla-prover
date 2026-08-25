---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: n is any natural in the finite range
Init == n \in NatOverride

\* Next-state relation: nondeterministically choose any value in the finite range
Next == n' \in NatOverride

\* Specification used by TLC
SPECIFICATION == Init /\ [][Next]_<<n>>

\* Aliases required by the configuration
INIT == Init
NEXT == Next

\* Invariant stating that double of n is even
EvenDouble == (2 * n) % 2 = 0

INVARIANTS == EvenDouble
PROPERTIES == EvenDouble
====
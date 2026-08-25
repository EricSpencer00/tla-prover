---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

VARIABLE n

\* Finite version of Nat used for model checking
NatOverride == 0 .. MaxNat

\* Evenness predicate
Even(m) == m % 2 = 0

\* Initial condition: n ranges over the finite natural numbers
Init == n \in NatOverride

\* No state change; the property is checked on the initial state
Next == UNCHANGED n

\* Full specification
SPECIFICATION == Init /\ [][Next]_<<n>>

\* Invariant stating that double any n is even
INVARIANTS == Even(2 * n)

\* Property (identical to the invariant for this simple check)
PROPERTIES == Even(2 * n)

====
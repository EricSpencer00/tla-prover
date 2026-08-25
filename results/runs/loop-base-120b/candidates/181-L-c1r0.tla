---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat

\* Finite version of the natural numbers, bounded by MaxNat
NatOverride == 0 .. MaxNat

VARIABLES n

\* Initial state: n starts at 0 and is within the bounded naturals
Init == /\ n \in NatOverride
        /\ n = 0

\* Simple next-step action that increments n, staying within the bound
Next == /\ n' \in NatOverride
        /\ n' = n + 1

\* Full specification used by TLC
SPECIFICATION == Init /\ [][Next]_<<n>>

\* Invariant stating that the double of any natural number in the range is even
INVARIANTS == \A m \in NatOverride : (2 * m) % 2 = 0

\* Property (theorem) to be checked; identical to the invariant here
PROPERTIES == INVARIANTS

====
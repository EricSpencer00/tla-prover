---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* Assumed theorem: double of any natural number is even
THEOREM == \A n \in NatOverride : (2 * n) % 2 = 0

\* Trivial state (no variables)
INIT == TRUE
NEXT == UNCHANGED <<>>

SPECIFICATION == INIT /\ [][NEXT]_<<>>

INVARIANTS == THEOREM
PROPERTIES == THEOREM
====
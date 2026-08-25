---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

ASSUME MaxNat \in Nat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: n is any natural number within the bounded range
Init == n \in NatOverride

\* Next-state relation: n may nondeterministically take any value in the bounded range
Next == /\ n' \in NatOverride
        /\ UNCHANGED << >>

\* Exported identifiers required by the .cfg
INIT == Init
NEXT == Next
SPECIFICATION == Init /\ [][Next]_<<n>>
EvenDouble == \A n \in NatOverride : \E k \in NatOverride : n + n = 2 * k
INVARIANTS == EvenDouble
PROPERTIES == EvenDouble

====
---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

VARIABLE v

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* Predicate expressing that a number is even using the finite NatOverride
Even(x) == \E k \in NatOverride : x = 2 * k

\* Initial state: the variable ranges over the finite naturals
Init == v \in NatOverride

\* Next-state relation: the variable can take any value in the finite range
Next == /\ v' \in NatOverride

\* The overall specification
SPECIFICATION == Init /\ [][Next]_<<v>>

\* Required identifiers
INIT == Init
NEXT == Next
INVARIANTS == TRUE
PROPERTIES == \A n \in NatOverride : Even(2 * n)

====
---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

CONSTANT MaxNat

(*\* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(*\* Predicate that a number is even using the finite NatOverride *)
Even(x) == \E k \in NatOverride : x = 2 * k

VARIABLES n

Init == n \in NatOverride

Next == n' \in NatOverride

SPECIFICATION == Init /\ [][Next]_<<n>>

INVARIANTS == Even(2 * n)

PROPERTIES == Even(2 * n)

====
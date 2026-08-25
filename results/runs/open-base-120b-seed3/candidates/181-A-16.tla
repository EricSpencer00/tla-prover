---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

VARIABLE n

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

Even(x) == x % 2 = 0

Init == n \in NatOverride

Next == n' \in NatOverride

SPECIFICATION == Init /\ [][Next]_<<n>>

INVARIANTS == Even(2 * n)

PROPERTIES == \A m \in NatOverride : Even(2 * m)

====
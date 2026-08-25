---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

NatOverride == 0 .. MaxNat

VARIABLE n

Even(x) == ∃ k \in Nat : x = 2 * k

INIT == n \in NatOverride

NEXT == n' \in NatOverride

SPECIFICATION == INIT /\ [][NEXT]_<<n>>

INVARIANTS == Even(2 * n)

PROPERTIES == \A n \in NatOverride : Even(2 * n)

====
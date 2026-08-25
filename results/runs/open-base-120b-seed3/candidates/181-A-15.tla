---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

NatOverride == 0..MaxNat

VARIABLE n

INIT == /\ n \in Nat

NEXT == /\ n \in Nat /\ n' \in Nat /\ n' = n + 1

DoubleEven == (2 * n) % 2 = 0

INVARIANTS == DoubleEven

PROPERTIES == DoubleEven

SPECIFICATION == INIT /\ [][NEXT]_<<n>>

====
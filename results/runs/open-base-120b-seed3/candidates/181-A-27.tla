---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

NatOverride == 0..MaxNat

VARIABLE n

INIT == n \in Nat

Even(m) == \E k \in Nat : m = 2 * k

NEXT == UNCHANGED n

SPECIFICATION == INIT /\ [][NEXT]_<<n>>

INVARIANTS == << Even(2 * n) >>

PROPERTIES == << >>

====
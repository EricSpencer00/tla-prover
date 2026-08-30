---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

CONSTANTS MaxNat

VARIABLES n

vars == <<n>>

Spec == Init /\ [][Next]_vars

Init == n = 0

Next == n < MaxNat /\ n' = n + 1

TypeOK == n \in 0..MaxNat

NatOverride == Nat

====
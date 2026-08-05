---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0..MaxNat

ASSUME Nat = NatOverride

VARIABLES n

vars == <<n>>

Init == n = 0

Next == \E m \in Nat : n' = m

Spec == Init /\ [][Next]_vars

NatBound == n \in Nat

====
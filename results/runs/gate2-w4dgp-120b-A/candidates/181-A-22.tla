---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

VARIABLES n
vars == <<n>>

NatOverride == 0..MaxNat

Init == n = 0
Next == n < MaxNat /\ n' = 1 + n
EvenDouble == 2 * n = n + n

Spec == Init /\ [][Next]_vars
====
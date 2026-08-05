---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

ASSUME MaxNat \in Nat /\ MaxNat >= 1

NatOverride == 0..MaxNat

VARIABLES n

vars == <<n>>

Init == n \in NatOverride

CheckDouble == 2 * n \in Nat /\ n \in NatOverride

Next == \E k \in NatOverride : n' = k

Spec == Init /\ [][CheckDouble]_vars /\ WF_vars(Next)

====
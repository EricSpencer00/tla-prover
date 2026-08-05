---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0 .. MaxNat

ASSUME MaxNat \in Nat

VARIABLES n

vars == <<n>>

InitState == n = 0

Init == InitState

SumStep == n' = n + 1

Next == SumStep

Spec == Init /\ [][SumStep]_vars

EvenDouble == \A m \in NatOverride : 2 * m \in Nat

====
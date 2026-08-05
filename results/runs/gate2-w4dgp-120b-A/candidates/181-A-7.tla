---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0..MaxNat

ASSUME MaxNat \in Nat /\ MaxNat >= 1

VARIABLES x

vars == <<x>>

Init == x = 0

Next == x' = x + 1 \/ x' = 0

Spec == Init /\ [][Next]_vars

BoundedRange == \A x \in {0, 1, 2} : TRUE

====
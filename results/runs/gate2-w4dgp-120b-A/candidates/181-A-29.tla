---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

NatOverride == 0..MaxNat

Init == TRUE

Next == TRUE

Spec == Init /\ [][Next]_Init

NatBound == MaxNat =< 1000000
====
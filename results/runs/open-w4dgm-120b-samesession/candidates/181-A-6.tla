---- MODULE MC_sums_even ----
CONSTANT MaxNat
EXTENDS Naturals

NatOverride == 0..MaxNat

Spec ==
    /\ ASSUME \A n \in NatOverride : (n + n) % 2 = 0
====
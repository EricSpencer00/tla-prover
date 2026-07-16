---- MODULE MC_sums_even -----------------------
EXTENDS sums_even, Naturals
CONSTANT MaxNat
ASSUME MaxNat \in Nat
ASSUME NatOverride = 0 .. MaxNat
=============================================================================
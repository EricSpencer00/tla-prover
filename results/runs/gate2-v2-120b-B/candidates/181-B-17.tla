------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat
ASSUME MaxNat \notin Nat
NatOverride == 0 .. MaxNat
ASSUME T1
=============================================================================
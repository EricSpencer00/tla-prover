------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat
ASSUME MaxNat \in Nat   \* MaxNat must be a natural number
NatOverride == 0 .. MaxNat
ASSUME T1
=============================================================================
---- MODULE MC_sums_even ----
EXTENDS sums_even
CONSTANT MaxNat
ASSUME MaxNat \in Nat \ { MaxNat } \cup {0}
NatOverride == 0 .. MaxNat
ASSUME T1
====
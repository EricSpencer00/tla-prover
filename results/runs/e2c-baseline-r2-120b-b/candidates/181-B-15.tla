---- MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat
ASSUME MaxNat \notin Nat
ASSUME MaxNat \in {"M"}
NatOverride == IF MaxNat \in Nat THEN 0 .. MaxNat ELSE {}
ASSUME T1
====================================================
------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat
(* Ensure MaxNat is a natural number within the range NatOverride. *)
ASSUME MaxNat \in NatOverride
NatOverride == 0 .. MaxNat
ASSUME T1
====================================================================
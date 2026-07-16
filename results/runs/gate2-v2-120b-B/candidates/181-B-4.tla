------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even

CONSTANT MaxNat

(* Ensure MaxNat is a natural number within the usual natural numbers set *)
ASSUME MaxNat \in Nat

(* Define the overridden natural numbers set to range from 0 up to MaxNat *)
NatOverride == 0 .. MaxNat

(* Preserve the original assumption from the extended module *)
ASSUME T1
====================================================================
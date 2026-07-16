---- MODULE MC_sums_even ----
EXTENDS sums_even

CONSTANT MaxNat

(* MaxNat must be a natural number *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

ASSUME T1
====
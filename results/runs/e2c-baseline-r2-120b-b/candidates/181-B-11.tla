---- MODULE MC_sums_even ----
EXTENDS sums_even

(* Define MaxNat as a negative integer so that it is not a natural number. *)
MaxNat == -1

ASSUME MaxNat \notin Nat

NatOverride == 0 .. MaxNat

ASSUME T1
====
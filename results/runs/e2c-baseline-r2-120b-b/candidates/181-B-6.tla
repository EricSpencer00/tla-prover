---- MODULE MC_sums_even ----
EXTENDS sums_even

(* Define MaxNat as a concrete value that is not a natural number. *)
MaxNat == -1

NatOverride == 0 .. MaxNat

ASSUME MaxNat \notin Nat
ASSUME T1
====================================================================
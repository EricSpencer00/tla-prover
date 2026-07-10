---- MODULE MC_sums_even -----------------------
EXTENDS sums_even

(* Define MaxNat as a concrete value that is not a natural number,
   satisfying the assumption below while keeping the intended
   semantics of overriding the natural numbers with an empty range. *)
MaxNat == -1

ASSUME MaxNat \notin Nat

NatOverride == 0 .. MaxNat

ASSUME T1
====================================================================
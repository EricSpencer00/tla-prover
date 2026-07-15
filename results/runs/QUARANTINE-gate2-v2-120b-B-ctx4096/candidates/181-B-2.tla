---- MODULE MC_sums_even -----------------------
EXTENDS sums_even

(* The constant MaxNat must be a natural number. *)
CONSTANT MaxNat

(* Enforce that MaxNat belongs to the set of natural numbers. *)
ASSUME MaxNat \in Nat

====
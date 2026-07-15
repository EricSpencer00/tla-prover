---- MODULE MC_sums_even ----
EXTENDS sums_even
CONSTANT MaxNat

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

(* The original module assumed MaxNat ∉ Nat, which made the model
   immediately inconsistent because MaxNat was used to define a range
   of natural numbers.  Replacing that assumption with MaxNat ∈ Nat
   restores consistency while preserving the intended meaning:
   MaxNat now correctly bounds the natural-number range NatOverride. *)

====
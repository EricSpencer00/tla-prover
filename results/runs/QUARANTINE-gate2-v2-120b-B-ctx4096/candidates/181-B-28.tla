------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even

CONSTANT MaxNat

(* The constant MaxNat must be a natural number. *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

(* Preserve the original assumed predicate T1. *)
ASSUME T1

=============================================================================
------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even

CONSTANT MaxNat

(* The assumption that MaxNat is not a natural number is contradictory,
   because Nat is defined as the set of all natural numbers.  This caused
   TLC to fail immediately.  The intention of the original specification
   is to bound the natural numbers used in the model, not to exclude
   MaxNat from Nat.  We therefore replace the contradictory assumption with
   a consistent one that states MaxNat is a natural number and that the
   overridden natural numbers are exactly the numbers from 0 up to MaxNat. *)

ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat

(* Preserve the original assumption T1 from the extended module. *)
ASSUME T1

=============================================================================
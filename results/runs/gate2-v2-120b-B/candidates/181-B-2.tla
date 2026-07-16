---- MODULE MC_sums_even ----
EXTENDS sums_even

(* The original specification assumed MaxNat ∉ Nat, which is contradictory
   because Nat is the set of all natural numbers. Since MaxNat is meant to
   bound the overrides for Nat, we replace the erroneous assumption with a
   direct definition of NatOverride that respects the intended bound. *)

CONSTANT MaxNat
NatOverride == 0 .. MaxNat

(* Preserve the original assumption T1 from the extended module. *)
ASSUME T1

====
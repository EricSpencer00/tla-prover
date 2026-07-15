---- MODULE MC_sums_even -----------------------
EXTENDS sums_even

CONSTANT MaxNat

(* Ensure MaxNat is a natural number. *)
ASSUME MaxNat \in Nat

(* NatOverride is the set of natural numbers up to MaxNat. *)
NatOverride == 0 .. MaxNat

(* The original assumption T1 is kept unchanged. *)
ASSUME T1
====
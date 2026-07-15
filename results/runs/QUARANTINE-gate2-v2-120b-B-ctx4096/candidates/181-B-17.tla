------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat

(* The original specification incorrectly assumed that MaxNat is not a natural
   number, which caused TLC to abort because the assumption was false.
   Since MaxNat is meant to specify the upper bound of a finite range of
   natural numbers, we must require that it is indeed a natural number.
   This change corrects the assumption while preserving the intended semantics
   of the module. *)

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

ASSUME T1
====================================================================
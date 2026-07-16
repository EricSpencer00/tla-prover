---- MODULE MC_sums_even ----
EXTENDS sums_even

(* 
  The original specification incorrectly assumed that MaxNat is not a natural 
  number, which caused TLC to abort with a false assumption. 
  Since the model is intended to explore natural numbers up to MaxNat, 
  we replace the failing assumption with a correct one that asserts MaxNat 
  belongs to Nat (the set of natural numbers). This change preserves the 
  intended semantics of the system while allowing the model to be checked. 
*)
CONSTANT MaxNat
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

(* Preserve any module-specific assumptions that are required for the model. *)
ASSUME T1

====
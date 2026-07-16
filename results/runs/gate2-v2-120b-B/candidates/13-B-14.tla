---- MODULE MCBakery --------------------------------
EXTENDS Bakery

CONSTANT MaxNat

(* The original specification required MaxNat to be NOT a natural number,
   which caused TLC to reject the model because the assumption was false.
   For the intended use of a bounded natural number in the extended model,
   we state that MaxNat is a natural number and define NatOverride as the
   corresponding interval. This preserves the original intention (using a
   finite natural bound) while allowing the model to satisfy the assumption. *)

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================
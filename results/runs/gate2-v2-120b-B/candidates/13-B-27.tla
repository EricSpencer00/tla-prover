---- MODULE MCBakery -------------------------------------------------
EXTENDS Bakery, Naturals

(* 
  This configuration introduces a constant MaxNat that must be a natural 
  number.  The original specification required MaxNat ∉ Nat, which made the 
  module inconsistent and caused TLC to abort during initialization. 
  We correct this by asserting that MaxNat is a natural number and then 
  defining NatOverride as the finite range 0..MaxNat.  This preserves the 
  intended use of NatOverride as a bounded set of natural numbers without 
  weakening any invariants or properties of the underlying Bakery module.
*)

CONSTANT MaxNat

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================
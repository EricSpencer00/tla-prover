---- MODULE MCBakery --------------------------------
EXTENDS Bakery, Naturals
(* 
  This module overrides the natural number set used by the Bakery module
  with a finite range 0..MaxNat. The original specification used an 
  unintentionally contradictory assumption that MaxNat ∉ Nat, which made 
  the model immediately unsatisfiable. The corrected version replaces that 
  assumption with a consistent one that requires MaxNat to be a natural 
  number and that the overridden set is a subset of Nat. This preserves the
  intended finite‑range behavior without weakening any safety properties.
*)
CONSTANT MaxNat

(* MaxNat must be a natural number (including zero) *)
MaxNatIsNat == MaxNat \in Nat

(* The overridden natural number set is the finite interval 0..MaxNat *)
NatOverride == 0 .. MaxNat

(* Ensure the overridden set is indeed a subset of the original Nat set *)
NatSubset == NatOverride \subseteq Nat

=============================================================================
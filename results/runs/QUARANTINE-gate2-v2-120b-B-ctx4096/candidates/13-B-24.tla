---------------------------- MODULE MCBakery --------------------------------
EXTENDS Bakery

(* The constant MaxNat must be a natural number in order for NatOverride
   to be a well‑formed subset of Nat. *)
CONSTANT MaxNat
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat
=============================================================================
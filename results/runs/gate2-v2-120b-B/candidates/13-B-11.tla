---- MODULE MCBakery ----
EXTENDS Bakery
CONSTANT MaxNat

(* MaxNat must be a natural number, otherwise the model is vacuous. *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================
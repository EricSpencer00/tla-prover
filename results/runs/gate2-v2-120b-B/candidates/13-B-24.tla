---- MODULE MCBakery --------------------------------
EXTENDS Bakery

CONSTANT MaxNat

(* Ensure that MaxNat is a natural number and define NatOverride accordingly. *)
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat

=============================================================================
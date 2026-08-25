---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS MaxNat

(* Finite version of the natural numbers, used to override Nat in the model checker *)
NatOverride == 0 .. MaxNat
====
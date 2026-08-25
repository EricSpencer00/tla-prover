---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite version of the natural numbers used in the model *)
NatOverride == 0 .. MaxNat

====
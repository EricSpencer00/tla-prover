---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

====
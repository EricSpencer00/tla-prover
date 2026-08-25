---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* Finite version of the natural numbers used for model checking *)
NatOverride == 0 .. MaxNat

(* Inductive specification: reuse the specification defined in the Bakery module *)
ISpec == Spec

====
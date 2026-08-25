---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

(* Specification used by the .cfg file *)
ISpec == Spec

(* Optional aliases for convenience; they refer to the definitions in Bakery *)
INIT == Init
NEXT == Next

====
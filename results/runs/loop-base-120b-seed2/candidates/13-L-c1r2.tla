---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite version of the natural numbers used in the model *)
NatOverride == 0 .. MaxNat

(* Specification used by the .cfg *)
ISpec == Spec

(* Invariants required by the .cfg *)
MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

====
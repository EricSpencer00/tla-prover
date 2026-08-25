---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Specification (inductive) *)
ISpec == Bakery!Spec

(* Inherited invariants *)
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv
====
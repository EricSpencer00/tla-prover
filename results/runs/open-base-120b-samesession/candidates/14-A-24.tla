---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Specification and invariants inherited from Boulanger *)
Spec == Boulanger.Spec

MutualExclusion == Boulanger.MutualExclusion
TypeOK == Boulanger.TypeOK
Inv == Boulanger.Inv
====
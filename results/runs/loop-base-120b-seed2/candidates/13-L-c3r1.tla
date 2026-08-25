---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite replacement for the infinite set of natural numbers *)
NatOverride == 0 .. MaxNat

(* Export the invariants required by the .cfg file *)
MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

(* Inductive specification (uses the overridden Nat) *)
ISpec == Spec

====
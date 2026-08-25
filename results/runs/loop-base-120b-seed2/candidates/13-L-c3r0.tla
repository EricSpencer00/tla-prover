---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite replacement for the infinite set of natural numbers *)
NatOverride == 0 .. MaxNat

(* Inductive specification (uses the overridden Nat) *)
ISpec == Spec

====
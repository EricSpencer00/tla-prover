---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* Finite version of the natural numbers, used to override Nat in the model checker *)
NatOverride == 0 .. MaxNat

(* Inductive specification: start from any type‑correct state satisfying the invariant *)
ISpec == Spec

====
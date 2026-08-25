---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Inductive specification: any type‑correct state satisfying the invariant can be an initial state *)
ISpec == (TypeOK /\ Inv) /\ [] [Next]_vars

====
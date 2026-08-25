---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Inductive specification: start from any type‑correct state satisfying the invariant *)
ISpec == (TypeOK /\ Inv) /\ [] [Next]_vars

====
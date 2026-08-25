---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Re‑export the invariants and safety property from the Bakery module *)
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

(* Inductive specification: start from any type‑correct state satisfying the invariant *)
ISpec == (TypeOK /\ Inv) /\ [] [Next]_vars

====
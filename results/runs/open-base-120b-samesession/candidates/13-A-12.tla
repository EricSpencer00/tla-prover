---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Inductive specification: start from any type‑correct state satisfying the invariant *)
ISpec == TypeOK /\ Inv /\ [][Next]_vars

(* Invariants inherited from the Bakery specification *)
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

====
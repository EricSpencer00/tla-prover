---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Inherited state definitions *)
Init == Bakery!Init
Next == Bakery!Next

(* Inductive specification: any type‑correct state satisfies the invariant and all steps preserve it *)
ISpec == TypeOK /\ [][Next]_vars

(* Invariants imported from the Bakery specification *)
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

====
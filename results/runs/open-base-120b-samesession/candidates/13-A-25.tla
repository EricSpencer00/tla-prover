---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N
CONSTANT MaxNat

(* Finite version of the natural numbers used during model checking *)
NatOverride == 0 .. MaxNat

(* Inductive specification: start from any state satisfying the invariant *)
ISpec == Init \/ (Inv /\ [][Next]_vars)

(* Invariants required by the configuration *)
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

====
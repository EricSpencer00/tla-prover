---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite version of the natural numbers, used to bound ticket values *)
NatOverride == 0 .. MaxNat

(* Inductive specification: start from any state satisfying the invariant *)
ISpec == Init /\ [][Next]_vars

(* Invariants required by the .cfg file *)
MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

====
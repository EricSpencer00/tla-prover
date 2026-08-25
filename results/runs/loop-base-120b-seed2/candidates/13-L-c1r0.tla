---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite version of the natural numbers used in the model *)
NatOverride == 0 .. MaxNat

(* Inductive specification: start from any type‑correct state and 
   require that every step respects the Next relation *)
ISpec == TypeOK /\ [][Next]_vars

(* Invariants required by the configuration *)
MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

====
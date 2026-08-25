---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

(* Inductive specification: start from any type‑correct state and
   require that every step preserves the invariant. *)
ISpec == TypeOK /\ [][Next]_vars

(* Invariants inherited from the Bakery specification *)
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

====
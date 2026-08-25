---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* Finite replacement for the infinite set of natural numbers *)
NatOverride == 0 .. MaxNat

(* Invariants inherited from the Bakery specification *)
MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

(* Inductive specification: start from any type‑correct state satisfying the
   invariant and require the invariant to hold after every step. *)
ISpec == (Init /\ TypeOK) \/ [] (TypeOK /\ [][Next]_vars)

====
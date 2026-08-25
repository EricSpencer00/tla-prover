---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite replacement for the infinite set of natural numbers *)
NatOverride == 0 .. MaxNat

(* Aliases for invariants defined in the Bakery module *)
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

(* Inductive specification: start from any type‑correct state and
   require that every step satisfies the Next relation. *)
ISpec == TypeOK /\ [][Next]_vars

====
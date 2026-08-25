---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets, Bakery

CONSTANTS N, MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

(* Inductive specification: start from any state satisfying the invariant *)
ISpec == (Init \/ (TypeOK /\ Inv)) /\ [][Next]_vars

(* Invariants required by the configuration *)
MutualExclusion == Bakery.MutualExclusion
TypeOK == Bakery.TypeOK
Inv == Bakery.Inv
====
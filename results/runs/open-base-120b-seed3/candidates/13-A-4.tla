---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite version of the natural numbers, to be used in place of Nat *)
NatOverride == 0 .. MaxNat

(* Inductive specification: start from any type‑correct state and follow Next *)
ISpec == TypeOK /\ [][Next]_vars

====
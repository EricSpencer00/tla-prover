---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Inductive specification: start from any state satisfying the invariant *)
ISpec == Init \/ (Inv /\ [][Next]_vars)

====
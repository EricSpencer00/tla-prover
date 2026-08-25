---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANT N, MaxNat

(* Finite version of the natural numbers used for model checking *)
NatOverride == 0 .. MaxNat

(* Include the original Bakery specification *)
INSTANCE Bakery

(* Inductive specification: start from any state satisfying the invariant *)
ISpec == (TypeOK /\ Inv) /\ [][Next]_vars

====
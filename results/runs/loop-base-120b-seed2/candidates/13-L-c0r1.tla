---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT MaxNat

(* Finite version of the natural numbers, used to override Nat in the model. *)
NatOverride == 0 .. MaxNat

(* Inductive specification: allows any state satisfying the invariant as a start. *)
ISpec == Init \/ (Inv /\ [][Next]_vars)

====
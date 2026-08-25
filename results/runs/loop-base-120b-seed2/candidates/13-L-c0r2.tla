---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite version of natural numbers, used to override Nat in the model. *)
NatOverride == 0 .. MaxNat

(* Aliases to the invariants defined in the Bakery module. *)
MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

(* Inductive specification: allows any state satisfying the invariant as a start. *)
ISpec == Init \/ (Inv /\ [][Next]_vars)

====
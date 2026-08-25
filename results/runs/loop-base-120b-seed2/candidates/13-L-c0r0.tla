---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite version of the natural numbers, used to override Nat in the model. *)
NatOverride == 0 .. MaxNat

(* Aliases to the definitions from the Bakery specification. *)
Init == Bakery!Init
Next == Bakery!Next

MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

(* Inductive specification: allows any state satisfying the invariant as a start. *)
ISpec == Init \/ (Inv /\ [][Next]_vars)

====
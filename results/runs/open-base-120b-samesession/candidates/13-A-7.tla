---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

(* Invariants inherited from the Bakery specification *)
MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

(* Inductive specification using the inherited Init, Next, and vars *)
ISpec == Init /\ [][Next]_vars

====
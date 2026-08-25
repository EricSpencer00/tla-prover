---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* Finite version of the natural numbers, used via the .cfg replacement *)
NatOverride == 0 .. MaxNat

(* Inherit the initial predicate and next-state relation from the Bakery module *)
Init == Bakery!Init
Next == Bakery!Next

(* Specification used by the model checker *)
ISpec == Init /\ [][Next]_vars

====
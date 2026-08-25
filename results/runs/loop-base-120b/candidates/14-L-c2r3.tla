---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

(* Finite version of the natural numbers for model checking. *)
NatOverride == 0 .. MaxNat

(* Re‑export the specification and its invariants from Boulanger. *)
Spec == Boulanger!Spec
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====
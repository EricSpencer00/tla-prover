---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

(* Finite version of the natural numbers for model checking. *)
NatOverride == 0 .. MaxNat

(* Re‑expose the identifiers required by the .cfg file. *)
Spec == Boulanger!Spec
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====
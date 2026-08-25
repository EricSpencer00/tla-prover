---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

(* Finite version of the natural numbers for model checking. *)
NatOverride == 0 .. MaxNat

====
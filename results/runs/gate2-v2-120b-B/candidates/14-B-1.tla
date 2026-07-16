--------------------------- MODULE MCBoulanger ------------------------------
EXTENDS Boulanger

CONSTANT MaxNat

(* MaxNat must be a natural number. *)
ASSUME NatOverride == MaxNat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
=============================================================================
---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* Ensure MaxNat is a natural number. *)
ASSUME NatOverride = 0 .. MaxNat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat

====
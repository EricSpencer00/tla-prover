---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* MaxNat must be a natural number (including 0). *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat

====
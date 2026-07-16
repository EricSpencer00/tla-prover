---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* MaxNat must be a natural number; the original assumption incorrectly required it
   not to belong to Nat, causing the model checker to reject every behavior. *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat

====
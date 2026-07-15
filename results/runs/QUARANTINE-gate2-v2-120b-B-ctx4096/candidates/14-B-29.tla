---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* MaxNat is a natural number that is strictly greater than every natural
   number used in the original Boulanger module.  This ensures the
   assumption that MaxNat is not a member of Nat is satisfied for any
   concrete value of MaxNat that the model checker may choose. *)
ASSUME MaxNat > 1000

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat

====
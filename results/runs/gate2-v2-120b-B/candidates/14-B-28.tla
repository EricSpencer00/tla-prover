---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* MaxNat must be a natural number. *)
ASSUME MaxNat \in Nat

(* Override the natural numbers used by the model up to MaxNat. *)
NatOverride == 0 .. MaxNat

(* Ensure that all processes keep their counters strictly below MaxNat. *)
StateConstraint == \A process \in Procs : num[process] < MaxNat

====
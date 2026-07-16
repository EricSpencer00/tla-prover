---- MODULE MCBoulanger -------------------------------------------------
EXTENDS Boulanger

CONSTANT MaxNat

(* The constant MaxNat is required to be a natural number. *)
ASSUME MaxNat \in Nat

(* NatOverride is the set of natural numbers up to MaxNat. *)
NatOverride == 0 .. MaxNat

(* StateConstraint ensures that each process's count stays below MaxNat. *)
StateConstraint == \A process \in Procs : num[process] < MaxNat

=============================================================================
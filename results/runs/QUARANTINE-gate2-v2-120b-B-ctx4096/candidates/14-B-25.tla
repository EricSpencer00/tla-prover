---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* Ensure MaxNat is a natural number, as required by NatOverride and the state constraint. *)
ASSUME MaxNat \in Nat

(* NatOverride provides the valid range of values for natural-number variables. *)
NatOverride == 0 .. MaxNat

(* StateConstraint ensures that every process's counter stays strictly below MaxNat. *)
StateConstraint == \A process \in Procs : num[process] < MaxNat

====
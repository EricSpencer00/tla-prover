--------------------------- MODULE MCBoulanger ------------------------------
EXTENDS Boulanger

CONSTANT MaxNat

(* MaxNat is the greatest natural number allowed for the counter. *)
ASSUME MaxNat \in Nat

(* NatOverride is the set of all natural numbers up to MaxNat. *)
NatOverride == 0 .. MaxNat

(* StateConstraint enforces that each process's counter stays below MaxNat. *)
StateConstraint == \A process \in Procs : num[process] < MaxNat
=============================================================================
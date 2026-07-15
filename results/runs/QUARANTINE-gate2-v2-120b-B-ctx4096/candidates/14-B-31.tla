---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* MaxNat should be a natural number, not a member of Nat (the set of all naturals). *)
ASSUME MaxNat \in Nat

(* The set of values that num[process] is allowed to take. *)
NatOverride == 0 .. MaxNat

(* State constraint: each process's counter stays below MaxNat. *)
StateConstraint == \A process \in Procs : num[process] < MaxNat

====
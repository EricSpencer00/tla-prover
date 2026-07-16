---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* MaxNat is a natural number that is not already in Nat, i.e., it is
   strictly greater than every element of Nat. *)
ASSUME MaxNat \notin Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat

=============================================================================
--------------------------- MODULE MCBoulanger ------------------------------
EXTENDS Boulanger

CONSTANT MaxNat

ASSUME MaxNat \in Nat

(* The original spec defined NatOverride as 0..MaxNat and a StateConstraint
   that required each process's counter to be strictly less than MaxNat.
   Because MaxNat is now guaranteed to be a natural number, we can keep
   those definitions unchanged; they remain meaningful and do not affect
   the behavior of the Boulanger module. *)

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat

=============================================================================
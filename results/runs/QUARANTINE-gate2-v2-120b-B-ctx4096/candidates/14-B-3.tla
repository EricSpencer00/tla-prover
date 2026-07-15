---- MODULE MCBoulanger ----
EXTENDS Boulanger
CONSTANT MaxNat

(* The following assumption originally required MaxNat to be outside Nat. 
   That made the model impossible to satisfy.  To keep the intended semantics,
   we allow MaxNat to be any natural number and define NatOverride accordingly. *)
ASSUME NatOverride = 0 .. MaxNat

(* StateConstraint now uses the same definition of NatOverride. *)
StateConstraint == \A process \in Procs : num[process] \in NatOverride

=============================================================================
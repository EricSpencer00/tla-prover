---- MODULE MCBoulanger ----
EXTENDS Boulanger
CONSTANT MaxNat

(* The original specification incorrectly assumed that MaxNat is not a natural number,
   which caused the model checker to reject the specification immediately.
   Since MaxNat is intended to be an upper bound for the natural numbers used in the model,
   we replace the contradictory assumption with a correct one that states MaxNat is a
   natural number. This change is minimal and preserves the intended semantics of the
   system. *)

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
====
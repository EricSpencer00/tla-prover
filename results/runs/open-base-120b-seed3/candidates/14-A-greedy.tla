---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(* Finite version of the natural numbers set, used to override Nat in the model. *)
NatOverride == 0 .. MaxNat

(* State constraint: all ticket numbers must stay strictly below MaxNat. *)
StateConstraint == \A i \in 1 .. N : ticket[i] < MaxNat

(* Specification: inherit the full behavior from Boulanger and enforce the state constraint. *)
Spec == Boulanger!Spec /\ []StateConstraint

====
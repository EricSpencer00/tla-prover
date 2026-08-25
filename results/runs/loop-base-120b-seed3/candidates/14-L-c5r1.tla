---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

(* Include the Boulanger algorithm specification as an instance. *)
INSTANCE Boulanger

(* Finite version of the natural numbers used for model checking. *)
NatOverride == { i \in Nat : i <= MaxNat }

(* State constraint that keeps all ticket numbers strictly below MaxNat. *)
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

(* Specification and properties, with the state constraint added to the spec. *)
Spec == Boulanger!Spec /\ []StateConstraint
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====
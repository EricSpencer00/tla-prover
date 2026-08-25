---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

(* Finite version of the natural numbers used for model checking. *)
NatOverride == { i \in Nat : i <= MaxNat }

(* State constraint that keeps all ticket numbers strictly below MaxNat. *)
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

(* Specification and properties inherited from the Boulanger module. *)
Spec == Boulanger!Spec
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====
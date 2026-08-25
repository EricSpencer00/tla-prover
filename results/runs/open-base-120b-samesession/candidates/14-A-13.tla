---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0..MaxNat

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

(* Specification with the global state constraint *)
Spec == Boulanger!Spec /\ []StateConstraint

(* Invariants inherited from Boulanger *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====
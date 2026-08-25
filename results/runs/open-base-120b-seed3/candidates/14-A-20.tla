---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT N, MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0..MaxNat

(* State constraint: keep all ticket numbers strictly below MaxNat *)
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

(* Specification inherits Boulanger's behavior, constrained by the state constraint *)
Spec == Boulanger.Spec /\ StateConstraint

(* Invariants inherited from Boulanger, with the additional state constraint where appropriate *)
MutualExclusion == Boulanger.MutualExclusion
TypeOK          == Boulanger.TypeOK /\ StateConstraint
Inv             == Boulanger.Inv

====
---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0..MaxNat

\* State constraint: all ticket numbers must stay below MaxNat
StateConstraint == \A p \in Proc : ticket[p] < MaxNat

\* Specification for model checking (inherits Boulanger's Spec and adds the constraint)
Spec == Boulanger!Spec /\ StateConstraint

\* Invariants inherited from Boulanger
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====
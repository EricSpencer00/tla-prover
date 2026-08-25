---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT N, MaxNat

\* Finite version of the natural numbers (overrides Nat in the model)
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers stay below MaxNat
StateConstraint == \A i \in Proc : ticket[i] < MaxNat

\* Specification with the added state constraint
Spec == Boulanger!Spec /\ StateConstraint

\* Inherited invariants
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====
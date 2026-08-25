---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0..MaxNat

\* Instance of the original Boulanger specification
INSTANCE Boulanger

\* State constraint: ticket numbers must stay strictly below MaxNat
StateConstraint == \A i \in 1..N : Boulanger!ticket[i] < MaxNat

\* Specification (inherits Boulanger's behavior, adding the state constraint)
Spec == Boulanger!Spec /\ StateConstraint

\* Inherited invariants
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv
====
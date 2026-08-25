---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0..MaxNat

\* Instance of the original Boulanger specification
INSTANCE Boulanger AS B

\* State constraint: ticket numbers must stay strictly below MaxNat
StateConstraint == \A i \in 1..N : B!ticket[i] < MaxNat

\* Specification (inherits Boulanger's behavior, adding the state constraint)
Spec == B!Spec /\ StateConstraint

\* Inherited invariants
MutualExclusion == B!MutualExclusion
TypeOK           == B!TypeOK
Inv              == B!Inv
====
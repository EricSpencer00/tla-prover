---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANT N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* Instantiate the original Boulanger specification
INSTANCE Boulanger AS B

\* State constraint: all ticket numbers stay strictly below MaxNat
StateConstraint == \A i \in 1..N : B!ticket[i] < MaxNat

\* Full specification with the additional state constraint
Spec == B!Init /\ [][B!Next]_(B!vars) /\ []StateConstraint

\* Invariants inherited from Boulanger (exposed locally)
MutualExclusion == B!MutualExclusion
TypeOK == B!TypeOK
Inv == B!Inv
====
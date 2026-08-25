---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers stay below the maximum
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

\* Specification incorporating the state constraint
Spec == Boulanger!Spec /\ StateConstraint

\* Inherited invariants
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====
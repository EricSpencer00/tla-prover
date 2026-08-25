---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all tickets stay strictly below the maximum value
StateConstraint == 
    \A i \in 1..N : ticket[i] < MaxNat

\* Specification with the added state constraint
Spec == Boulanger!Spec /\ StateConstraint

\* Inherited invariants
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

====
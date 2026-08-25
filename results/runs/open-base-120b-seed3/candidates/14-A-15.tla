---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals, Temporal

CONSTANTS N, MaxNat

\* Finite version of the natural numbers set used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: every process ticket must stay strictly below MaxNat
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

\* Initial predicate (inherits Boulanger's Init and adds the constraint)
INIT == Boulanger!Init /\ StateConstraint

\* Next-state relation (inherits Boulanger's Next and adds the constraint)
NEXT == Boulanger!Next /\ StateConstraint

\* Full specification (adds the state constraint globally)
Spec == Boulanger!Spec /\ []StateConstraint

\* Invariants imported from the Boulanger specification
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv
====
---- MODULE MCBoulanger ----
EXTENDS Naturals
CONSTANT N, MaxNat

INSTANCE Boulanger

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: every process ticket must stay strictly below MaxNat
StateConstraint ==
    /\ \A i \in 1..N : Boulanger!ticket[i] < MaxNat

\* Specification with the constraint enforced in every reachable state
Spec == Boulanger!Spec /\ []StateConstraint

\* Export the required invariants from the instantiated Boulanger module
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv
====
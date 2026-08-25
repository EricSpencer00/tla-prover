---- MODULE MCBoulanger ----
EXTENDS Naturals
CONSTANT N, MaxNat

INSTANCE Boulanger AS B

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: every process ticket must stay strictly below MaxNat
StateConstraint ==
    /\ \A i \in 1..N : B!ticket[i] < MaxNat

\* Specification with the constraint enforced in every reachable state
Spec == B!Spec /\ []StateConstraint

\* Export the required invariants from the instantiated Boulanger module
MutualExclusion == B!MutualExclusion
TypeOK          == B!TypeOK
Inv             == B!Inv
====
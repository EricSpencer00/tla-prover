---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: every process ticket must stay strictly below MaxNat
StateConstraint ==
    /\ \A i \in 1..N: ticket[i] < MaxNat

\* Initial state with the constraint applied
InitC == Init /\ StateConstraint

\* Specification with the constraint enforced in every step
Spec == InitC /\ [][Next /\ StateConstraint]_vars

====
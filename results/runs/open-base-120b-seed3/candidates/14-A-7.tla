---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers stay strictly below MaxNat
StateConstraint == 
    /\ \A i \in 1..N: ticket[i] < MaxNat

\* Specification and invariants inherited from Boulanger
Spec == Boulanger!Spec

MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====
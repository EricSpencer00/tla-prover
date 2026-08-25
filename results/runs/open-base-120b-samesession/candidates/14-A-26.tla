---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* Specification and invariants inherited from Boulanger
Spec == Boulanger!Spec

MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

\* State constraint used by the .cfg (optional, but provided)
StateConstraint == \A i \in 1..N : Boulanger!ticket[i] < MaxNat
=============================================================================
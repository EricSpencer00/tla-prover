---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

\* Finite version of the natural numbers set for model checking
NatOverride == 0..MaxNat

\* Specification (inherited from Boulanger)
Spec == Boulanger!Spec

\* Inherited safety invariants
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====
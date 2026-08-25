---- MODULE MCBoulanger ----
EXTENDS Naturals
CONSTANTS N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Bring in the full Boulanger specification
INSTANCE Boulanger

\* Specification and its components required by the .cfg file
Spec == Boulanger!Spec
Init == Boulanger!Init
Next == Boulanger!Next

\* Invariants required by the .cfg file
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====
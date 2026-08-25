---- MODULE MCBoulanger ----
EXTENDS Naturals
CONSTANTS N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Bring in the full Boulanger specification
INSTANCE Boulanger AS B

\* Specification and its components required by the .cfg file
Spec == B!Spec
Init == B!Init
Next == B!Next

\* Invariants required by the .cfg file
MutualExclusion == B!MutualExclusion
TypeOK == B!TypeOK
Inv == B!Inv
====
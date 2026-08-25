---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Aliases to the definitions provided by the Bakery module
Init == Bakery!Init
Next == Bakery!Next

\* Inductive specification (used by the .cfg file)
ISpec == Bakery!Spec

\* Invariants required by the .cfg file
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv
====
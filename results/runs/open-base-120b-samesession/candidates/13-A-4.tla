---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* Override the infinite set Nat with a finite range for model checking
NatOverride == 0 .. MaxNat

\* Specification used for model checking (inductive specification)
ISpec == Spec

\* Invariants
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

====
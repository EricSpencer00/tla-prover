---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* Finite replacement for the infinite set Nat; used by the model checker via the .cfg replacement.
NatOverride == 0 .. MaxNat

\* Export the basic operators from the Bakery module under the names expected by the
\* configuration file.
Init == Bakery!Init
Next == Bakery!Next
ISpec == Bakery!Spec

\* Invariants required by the .cfg file.
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv
====
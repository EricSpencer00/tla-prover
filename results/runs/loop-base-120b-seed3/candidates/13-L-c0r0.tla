---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* Finite replacement for the infinite set of natural numbers
NatOverride == 0 .. MaxNat

\* Alias the definitions from the Bakery specification
Init == Bakery!Init
Next == Bakery!Next
vars == Bakery!vars

\* Specification used by the .cfg file
ISpec == Init /\ [][Next]_vars

\* Invariants required by the .cfg file
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv
====
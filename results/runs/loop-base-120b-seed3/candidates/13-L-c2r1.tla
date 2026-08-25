---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N
CONSTANT MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* Expose the required predicates from the Bakery module
MutualExclusion == Bakery!MutualExclusion
TypeOK           == Bakery!TypeOK
Inv              == Bakery!Inv

\* Inductive specification: start from any type‑correct state
ISpec == TypeOK /\ [] [Next]_vars

====
---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N
CONSTANT MaxNat

\* Finite replacement for the (infinite) Nat set used by the model checker
NatOverride == 0 .. MaxNat

\* Specification used for model checking (the inductive specification)
ISpec == Spec

====
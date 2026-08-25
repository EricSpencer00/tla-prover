---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N
CONSTANT MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

====
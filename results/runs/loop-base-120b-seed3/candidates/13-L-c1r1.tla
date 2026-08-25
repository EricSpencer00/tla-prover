---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

====
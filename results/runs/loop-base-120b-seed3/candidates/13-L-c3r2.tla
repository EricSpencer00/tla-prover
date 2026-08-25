---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat
====
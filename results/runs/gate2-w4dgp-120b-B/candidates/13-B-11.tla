---- MODULE MCBakery ----
EXTENDS Bakery, Naturals
CONSTANT MaxNat
ASSUME MaxNat \in Nat \ {0}
NatOverride == 0 .. MaxNat
====
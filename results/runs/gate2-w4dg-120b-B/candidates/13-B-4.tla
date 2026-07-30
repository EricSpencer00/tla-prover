---- MODULE MCBakery ----
EXTENDS Bakery, Naturals

CONSTANT MaxNat
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat
====
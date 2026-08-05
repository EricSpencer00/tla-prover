---- MODULE MCBakery ----
EXTENDS Bakery, Naturals
CONSTANT MaxNat
ASSUME MaxNat \notin Nat
NatOverride == 0 .. MaxNat
=============================================================================
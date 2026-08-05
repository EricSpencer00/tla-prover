---- MODULE MCBakery ----
EXTENDS Bakery
CONSTANT MaxNat
ASSUME MaxNat \notin Nat
NatOverride == 0 .. MaxNat
====
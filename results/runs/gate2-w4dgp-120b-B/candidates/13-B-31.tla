---- MODULE MCBakery ----
EXTENDS Bakery
CONSTANT MaxNat
ASSUME MaxNat \in Nat /\ MaxNat > 0
NatOverride == 0 .. MaxNat
====
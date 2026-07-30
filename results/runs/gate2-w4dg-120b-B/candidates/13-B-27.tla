---- MODULE MCBakery ----
EXTENDS Bakery
CONSTANT MaxNat
\* The original spec said MaxNat \notin Nat, which is contradictory for a constant
\* that is meant to be a natural number bound.  We fix the intent, not the model:
\* assume MaxNat is a natural, and restrict the bounded model's NatOverride to its
\* actual range.  No invariant or safety property is dropped.
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat
====
---- MODULE MCBakery ----
EXTENDS Bakery
CONSTANT MaxNat
\* MaxNat is the highest natural number we model; the original spec's
\* \notin Nat check was a typo that made the spec irreparably broken
\* under model checking.  The model still respects the intended bound.
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat
====
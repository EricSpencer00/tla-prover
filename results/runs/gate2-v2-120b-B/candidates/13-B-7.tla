---------------------------- MODULE MCBakery --------------------------------
EXTENDS Bakery

(*\* The original assumption incorrectly required MaxNat to be
    *outside* the natural numbers, which makes the model inconsistent.
    * We correct it by requiring MaxNat to be a natural number.
    *\*)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat
=============================================================================
---- MODULE MCBakery --------------------------------
EXTENDS Bakery
EXTENDS Naturals \* Ensure Nat is defined

CONSTANT MaxNat

\* MaxNat must be a natural number (non‑negative integer)
Nat := NatOverride

NatOverride == 0 .. MaxNat
=============================================================================
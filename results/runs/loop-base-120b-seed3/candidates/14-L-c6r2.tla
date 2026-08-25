---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

\* Finite version of Nat for model checking (values are 0 up to MaxNat‑1)
NatOverride == 0 .. MaxNat - 1
====
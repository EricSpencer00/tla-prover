---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS MaxNat

\* Finite version of the natural numbers set for model checking
NatOverride == 0..MaxNat
====
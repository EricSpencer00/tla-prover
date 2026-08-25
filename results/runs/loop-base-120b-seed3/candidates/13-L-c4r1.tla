---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\*  Finite replacement for the infinite set Nat used in the Bakery spec.
\*  The .cfg file substitutes Nat with NatOverride, therefore we provide
\*  a finite set of natural numbers ranging from 0 to MaxNat.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

====
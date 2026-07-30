---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* NatOverride replaces the infinite Nat from the standard module with a
\* bounded version, so TLC can check the theorem on a finite model.
NatOverride == { n \in Nat : n <= MaxNat }

SPECIFICATION == 1
INIT == 1
NEXT == 1
INVARIANTS == 1
PROPERTIES == 1

====
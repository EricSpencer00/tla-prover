--------------------------- MODULE MCBoulanger ------------------------------
EXTENDS Boulanger, Naturals

CONSTANT MaxNat
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
=============================================================================
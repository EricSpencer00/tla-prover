--------------------------- MODULE MCBoulanger ------------------------------
EXTENDS Boulanger

CONSTANT MaxNat

ASSUME NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
=============================================================================
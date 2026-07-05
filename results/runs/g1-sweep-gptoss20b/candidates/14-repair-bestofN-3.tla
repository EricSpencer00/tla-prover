---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat
CONSTANT Nat

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
=============================================================================
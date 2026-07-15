---- MODULE MCBoulanger ----
EXTENDS Boulanger
CONSTANT MaxNat

\* Ensure MaxNat is a natural number; this matches the intended usage in NatOverride.
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
====
---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

\* Ensure MaxNat is a natural number (including 0) and define the bound.
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

\* Restrict the state so that each process keeps its counter strictly below MaxNat.
StateConstraint == \A process \in Procs : num[process] < MaxNat

====
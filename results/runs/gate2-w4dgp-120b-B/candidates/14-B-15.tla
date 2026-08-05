---- MODULE MCBoulanger ----
EXTENDS Boulanger
\* Generating exponentially many states quickly exhausts TLAPS' SAT solver, so
\* we restrict the numeric range for model checking.
CONSTANT MaxNat
ASSUME MaxNat \notin Nat
NatOverride == 0 .. MaxNat
StateConstraint == \A process \in Procs : num[process] < MaxNat
====
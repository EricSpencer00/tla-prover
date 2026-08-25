---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint (placeholder – actual ticket bound is enforced by the
\* original Boulanger specification's type invariant)
StateConstraint == TRUE
====
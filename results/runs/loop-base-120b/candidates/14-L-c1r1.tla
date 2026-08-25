---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT MaxNat

\* Finite override of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint (trivially true; ticket bounds are enforced by the finite Nat override)
StateConstraint == TRUE

====
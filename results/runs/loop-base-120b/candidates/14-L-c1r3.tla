---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

\* ----------------------------------------------------------------------
\* Constant required by the configuration file
\* ----------------------------------------------------------------------
CONSTANT MaxNat

\* ----------------------------------------------------------------------
\* Finite override of the natural numbers used for model checking
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State constraint: keep all ticket numbers below the maximum value
\* ----------------------------------------------------------------------
StateConstraint == \A p \in 1..N: ticket[p] < MaxNat

====
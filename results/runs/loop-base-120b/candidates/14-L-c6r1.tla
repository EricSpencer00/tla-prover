---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers used for model checking.
\* The .cfg file will replace the standard Nat with NatOverride.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State constraint: keep every process ticket strictly below MaxNat.
\* (Can be used as a STATE_CONSTRAINT in the .cfg file.)
\* ----------------------------------------------------------------------
TicketBound == \A i \in 1..N : Boulanger!ticket[i] < MaxNat

====
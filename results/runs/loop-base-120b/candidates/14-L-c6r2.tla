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

\* ----------------------------------------------------------------------
\* Aliases for the specification and invariants defined in the Boulanger
\* module.  The .cfg file expects these identifiers to be present in the
\* current module.
\* ----------------------------------------------------------------------
Spec == Boulanger!Spec
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====
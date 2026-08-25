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
TicketBound == \A i \in 1..N : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Initialization and next-state relation inherited from Boulanger.
\* ----------------------------------------------------------------------
Init == Boulanger!Init
Next == Boulanger!Next
Vars == Boulanger!vars

\* ----------------------------------------------------------------------
\* Specification of the system.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Inherited safety invariants.
\* ----------------------------------------------------------------------
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv

====
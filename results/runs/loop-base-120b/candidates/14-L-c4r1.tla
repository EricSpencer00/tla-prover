---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers must stay strictly below MaxNat
TicketBound == 
    \A i \in 1 .. N : Boulanger!ticket[i] < MaxNat

\* Optional name for the state constraint (can be referenced in the .cfg)
StateConstraint == TicketBound

====
---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite override of the natural numbers set.
\* The model checker will assign MaxNat (e.g., 3) in the .cfg file.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State constraint: ticket numbers of all processes must stay below MaxNat.
\* This prunes states that would require numbers outside the finite range.
\* ----------------------------------------------------------------------
TicketBound == \A i \in 1 .. N : tickets[i] < MaxNat

\* ----------------------------------------------------------------------
\* Specification of the system.
\* It consists of the original Boulanger initialization and step relation,
\* together with the ticket bound constraint.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ TicketBound

====
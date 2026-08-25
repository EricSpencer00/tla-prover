---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: every process's ticket number must stay strictly below MaxNat
TicketBound == \A i \in 1..N : ticket[i] < MaxNat

\* Tuple of all state variables (as defined in the Boulanger specification)
vars == << pc, ticket, choosing >>

\* Full specification: initialization, next-step relation, and the state constraint
Spec == Init /\ [][Next]_vars /\ TicketBound

====
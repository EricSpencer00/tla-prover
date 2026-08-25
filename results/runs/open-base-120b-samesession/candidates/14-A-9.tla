---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers stay below the maximum value
TicketBound == 
    \A i \in 1..N : ticket[i] < MaxNat

\* Specification of the system (initial condition, next‑state relation,
\* and the state constraint)
Spec == Init /\ [][Next]_vars /\ []TicketBound

====
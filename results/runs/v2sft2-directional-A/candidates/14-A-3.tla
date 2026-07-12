---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANTS N, MaxNat, Nat

\* State constraint that keeps all ticket numbers strictly below the configured maximum
StateConstraint == \A i \in 1..N : Ticket[i] < MaxNat

\* Specification: initial condition, next-state relation, and the state constraint
Spec == Init /\ [][Next]_vars /\ StateConstraint

====
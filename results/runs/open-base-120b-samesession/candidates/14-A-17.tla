---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT N, MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers stay strictly below MaxNat
SC == \A i \in 1..N : ticket[i] < MaxNat

\* Specification of the system (initial state, next-state relation, and the state constraint)
Spec == Init /\ [][Next]_vars /\ []SC

=============================================================================
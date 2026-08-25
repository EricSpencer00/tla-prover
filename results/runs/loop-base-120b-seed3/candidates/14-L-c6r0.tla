---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* State constraint: ticket numbers must stay strictly below MaxNat
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

\* Specification with the state constraint added
Spec == Init /\ []StateConstraint /\ [][Next]_vars

====
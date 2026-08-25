---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N
CONSTANT MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: each process's ticket number stays strictly below MaxNat
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

\* The overall specification (initial condition, next‑state relation,
\* and the additional state constraint)
Spec == Init /\ [][Next]_(vars) /\ []StateConstraint

====
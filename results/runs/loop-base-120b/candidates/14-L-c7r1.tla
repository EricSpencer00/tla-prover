---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N
CONSTANT MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: each process's ticket number stays strictly below MaxNat
StateConstraint == \A i \in 1..N: ticket[i] < MaxNat

\* Aliases for the invariants defined in the Boulanger specification
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

\* The overall specification (initial condition and next‑state relation)
Spec == Init /\ [][Next]_vars /\ []StateConstraint

====
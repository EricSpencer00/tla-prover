---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers must stay strictly below MaxNat
StateConstraint == \A i \in 1..N: ticket[i] < MaxNat

\* Specification for model checking (initial condition, next‑state relation, and constraint)
Spec == Init /\ [][Next]_vars /\ StateConstraint

\* Invariants inherited from the Boulanger specification
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====
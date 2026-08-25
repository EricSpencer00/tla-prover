---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANT N
CONSTANT MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Bring in the original Boulanger specification without importing its
\* definitions directly (so we can augment them).
INSTANCE Boulanger AS B

\* State constraint: each process's ticket number stays strictly below MaxNat
StateConstraint == \A i \in 1..N : B!ticket[i] < MaxNat

\* Expose the invariants from the Boulanger specification under the
\* names expected by the .cfg file.
MutualExclusion == B!MutualExclusion
TypeOK          == B!TypeOK
Inv             == B!Inv

\* The overall specification (initial condition, next‑state relation,
\* and the additional state constraint)
Spec == B!Init /\ [][B!Next]_(B!vars) /\ []StateConstraint

====
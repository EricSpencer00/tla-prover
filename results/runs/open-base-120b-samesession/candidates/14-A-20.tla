---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* State constraint: ticket numbers must stay below the maximum
StateConstraint == \A i \in 1 .. N : ticket[i] < MaxNat

\* Export the basic components from the Boulanger specification
Init == Boulanger!Init
Next == Boulanger!Next

\* The full specification, enriched with the state constraint
Spec == Boulanger!Spec /\ StateConstraint

\* Invariants inherited from Boulanger
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

\* No additional liveness properties are defined for this configuration
Properties == {}

====
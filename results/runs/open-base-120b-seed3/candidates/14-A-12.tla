---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat

\* Finite version of the natural numbers set used for model checking
NatOverride == 0 .. MaxNat

\* Instantiate the original Boulanger specification
INSTANCE Boulanger AS Base WITH N <- N

\* State constraint: all ticket numbers stay strictly below MaxNat
StateConstraint == 
    \A i \in 1..N : ticket[i] < MaxNat

\* Specification with the added state constraint
Spec == Base!Spec /\ StateConstraint

\* Export the required invariants and properties
MutualExclusion == Base!MutualExclusion
TypeOK          == Base!TypeOK
Inv             == Base!Inv

====
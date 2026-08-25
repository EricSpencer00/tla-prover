---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers stay strictly below MaxNat
StateConstraint == 
  \A p \in 1 .. N : Boulanger!ticket[p] < MaxNat

\* Specification (inherits everything from Boulanger)
Spec == Boulanger!Spec

\* Invariants (inherited from Boulanger)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====
---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers stay below MaxNat
StateConstraint == 
  \A i \in 1..N : ticket[i] < MaxNat

\* Initialization inherits from Boulanger, augmented with the state constraint
Init == Boulanger!Init /\ StateConstraint

\* Next-state relation inherits from Boulanger, augmented with the state constraint
Next == Boulanger!Next /\ StateConstraint

\* Overall specification
Spec == Init /\ [][Next]_<<>> /\ []StateConstraint

\* Invariants (aliases to those defined in Boulanger)
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

====
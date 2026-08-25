---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0..MaxNat

\* Aliases to the definitions from Boulanger
Init == Boulanger!Init
Next == Boulanger!Next
Vars == Boulanger!vars

\* State constraint: all ticket numbers stay strictly below MaxNat
StateConstraint == \A i \in 1..N: ticket[i] < MaxNat

\* Full specification with the additional state constraint
Spec == Init /\ [][Next]_Vars /\ []StateConstraint

\* Invariants inherited from Boulanger
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====
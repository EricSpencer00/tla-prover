---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers stay strictly below MaxNat
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

\* Aliases for the definitions inherited from Boulanger
Init == Boulanger!Init
Next == Boulanger!Next
vars == Boulanger!vars

\* Specification used by the .cfg file
Spec == Init /\ [][Next]_vars /\ []StateConstraint

\* Invariants required by the .cfg file
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

====
---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

\* Finite override of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers must stay strictly below MaxNat
StateConstraint == 
    /\ \A i \in ProcSet : ticket[i] < MaxNat

\* Specification incorporating the state constraint
Spec == Init /\ [][Next]_vars /\ []StateConstraint

\* Invariants inherited from Boulanger
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

====
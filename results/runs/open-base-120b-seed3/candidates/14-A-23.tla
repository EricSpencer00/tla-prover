---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT N, MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers stay strictly below MaxNat
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

\* Specification used by TLC
Spec == Init /\ [][Next]_vars /\ []StateConstraint

\* Invariants inherited from Boulanger
MutualExclusion == MutualExclusion
TypeOK          == TypeOK
Inv             == Inv

====
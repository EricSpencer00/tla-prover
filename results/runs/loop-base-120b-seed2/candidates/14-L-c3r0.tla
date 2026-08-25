---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* Finite version of Nat for model checking
NatOverride == { n \in Nat : n <= MaxNat }

\* State constraint: all ticket numbers stay strictly below MaxNat
StateConstraint == 
    /\ \A i \in 1..N : ticket[i] < MaxNat

\* Re‑export the core components of the Boulanger specification
Init == Boulanger!Init
Next == Boulanger!Next
vars == Boulanger!vars

\* The specification to be checked by TLC
Spec == Init /\ StateConstraint /\ [][Next]_vars

\* Invariants inherited from Boulanger
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====
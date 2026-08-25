---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

\*--- Finite override for natural numbers ---------------------------------
NatOverride == 0 .. MaxNat

\*--- State constraint: all ticket numbers stay below MaxNat -------------
StateConstraint == 
    \A i \in 1 .. N : ticket[i] < MaxNat

\*--- Init and Next inherited from Boulanger, constrained by StateConstraint
Init == Boulanger!Init /\ StateConstraint

Next == Boulanger!Next /\ StateConstraint

\*--- Specification ---------------------------------------------------------
Spec == Init /\ [][Next]_(Boulanger!vars)

\*--- Invariants (aliases to those defined in Boulanger) --------------------
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

====
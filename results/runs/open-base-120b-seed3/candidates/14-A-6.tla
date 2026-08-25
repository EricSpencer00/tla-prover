---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* --- Finite override of the natural numbers ---
NatOverride == 0 .. MaxNat

\* --- Aliases for the Boulanger specification components ---
Init == Boulanger!Init
Next == Boulanger!Next

Spec == Init /\ [][Next]_vars

MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

\* --- State constraint: ticket numbers stay below the maximum ---
StateConstraint == 
    \A i \in ProcSet : ticket[i] < MaxNat

====
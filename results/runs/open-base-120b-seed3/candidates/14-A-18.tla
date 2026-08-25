---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

\* Finite version of natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers must stay strictly below MaxNat
StateConstraint == 
    \A i \in 1..N : tickets[i] < MaxNat

\* Overall specification (inherits Init, Next, and vars from Boulanger)
Spec == Init /\ [][Next]_vars

\* Invariants imported from Boulanger
MutualExclusion == Boulanger.MutualExclusion
TypeOK           == Boulanger.TypeOK
Inv              == Boulanger.Inv

====
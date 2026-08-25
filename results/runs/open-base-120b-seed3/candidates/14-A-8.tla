---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* State constraint: every process's ticket must stay strictly below MaxNat
TicketBound == \A i \in 1..N : ticket[i] < MaxNat
TicketBoundPrime == \A i \in 1..N : ticket'[i] < MaxNat

\* Initial predicate inherits Boulanger's Init and adds the ticket bound
Init == Boulanger!Init /\ TicketBound

\* Next-state relation inherits Boulanger's Next and enforces the bound after a step
Next == Boulanger!Next /\ TicketBoundPrime

\* Full specification
Spec == Init /\ [][Next]_Boulanger!vars

\* Invariants inherited from Boulanger
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====
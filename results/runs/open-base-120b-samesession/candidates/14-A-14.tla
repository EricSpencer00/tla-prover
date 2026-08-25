---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* Finite replacement for the infinite set Nat
NatOverride == 0 .. MaxNat

\* State constraint: all ticket numbers stay below MaxNat
TicketBound == \A i \in 1..N: ticket[i] < MaxNat

\* Initialization inherits Boulanger's Init and adds the ticket bound
Init == Boulanger.Init /\ TicketBound

\* Next-step relation inherits Boulanger's Next and adds the ticket bound
Next == Boulanger.Next /\ TicketBound

\* Full specification
Spec == Init /\ [][Next]_{Boulanger.vars}

\* Inherited safety invariants
MutualExclusion == Boulanger.MutualExclusion
TypeOK           == Boulanger.TypeOK
Inv              == Boulanger.Inv
====
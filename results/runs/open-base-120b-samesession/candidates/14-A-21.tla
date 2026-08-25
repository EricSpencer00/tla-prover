---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

\* Finite override of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* Specification: inherits Init, Next, and vars from Boulanger,
\* and adds a state constraint that all ticket numbers stay below MaxNat.
Spec == Init /\ [][Next]_(vars) /\ \A i \in 1..N: ticket[i] < MaxNat

\* Safety invariants inherited from the Boulanger specification
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv
====
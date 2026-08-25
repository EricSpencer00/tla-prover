---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

\*--- Finite version of Nat for model checking -----------------
NatOverride == 0 .. MaxNat

\*--- State constraint: all ticket numbers stay below MaxNat ----
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

\*--- Specification (original spec + state constraint) ---------
Spec == Boulanger!Spec /\ []StateConstraint

\*--- Exported invariants (taken from Boulanger) ---------------
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv

====
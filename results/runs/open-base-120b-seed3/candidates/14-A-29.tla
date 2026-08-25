---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

\* ----------------------------------------------------------------------
\* Finite override of the natural numbers set.
\* The .cfg file will replace Nat with NatOverride for model checking.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State constraint: all ticket numbers must stay strictly below MaxNat.
\* The .cfg file can refer to this operator as the state constraint.
\* ----------------------------------------------------------------------
TicketBound == \A i \in 1..N : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Specification: reuse the full behavioral spec from Boulanger.
\* ----------------------------------------------------------------------
Spec == Boulanger!Spec

\* ----------------------------------------------------------------------
\* Invariants inherited from Boulanger.
\* ----------------------------------------------------------------------
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv

====
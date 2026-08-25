---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(*--- Finite version of the natural numbers ---*)
NatOverride == 0 .. MaxNat

(*--- State constraint: ticket numbers stay strictly below MaxNat ---*)
TicketConstraint == \A i \in 1..N : ticket[i] < MaxNat

(*--- Specification (inherits Init and Next from Boulanger) ---*)
Spec == Boulanger!Spec

(*--- Invariants (exposed from Boulanger) ---*)
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

====
---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers for model checking.
\* The configuration file replaces the operator Nat with NatOverride.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State constraint: all ticket numbers must stay strictly below MaxNat.
\* This prevents the model from exploring states where a ticket would be
\* equal to the finite upper bound, which would break the intended
\* semantics of the original (infinite) Nat.
\* ----------------------------------------------------------------------
StateConstraint == \A i \in 1..N : Boulanger!ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Specification: inherits the full behavior from Boulanger and adds the
\* state constraint.
\* ----------------------------------------------------------------------
Spec == Boulanger!Spec /\ StateConstraint

\* ----------------------------------------------------------------------
\* Invariants inherited from the Boulanger specification.
\* ----------------------------------------------------------------------
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv
====
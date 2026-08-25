---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite override of the infinite set Nat.  The configuration replaces
\* uses of Nat with NatOverride, so we provide a finite set that is
\* suitable for model checking.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State constraint: every process ticket must stay strictly below MaxNat.
\* This constraint is conjoined to the initial predicate and to every
\* step of the algorithm.
\* ----------------------------------------------------------------------
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Init and Next are taken from the original Boulanger specification,
\* augmented with the state‑constraint.
\* ----------------------------------------------------------------------
Init == Boulanger!Init /\ StateConstraint
Next == Boulanger!Next /\ StateConstraint

\* ----------------------------------------------------------------------
\* Variable tuple used by the temporal operator.  It is taken from the
\* Boulanger module.
\* ----------------------------------------------------------------------
vars == Boulanger!vars

\* ----------------------------------------------------------------------
\* Specification required by the .cfg file.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================
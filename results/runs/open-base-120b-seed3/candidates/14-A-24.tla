---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite override of the natural numbers for model checking.
\* The .cfg file will replace Nat with NatOverride, so we provide a
\* finite set 0..MaxNat.
\* ----------------------------------------------------------------------
NatOverride == 0..MaxNat

\* ----------------------------------------------------------------------
\* State constraint: all ticket numbers must stay strictly below MaxNat.
\* This predicate will be used as a model‑checking constraint.
\* ----------------------------------------------------------------------
StateConstraint == \A i \in ProcSet : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Specification (initial condition, next‑state relation, and state constraint)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ []StateConstraint

=============================================================================
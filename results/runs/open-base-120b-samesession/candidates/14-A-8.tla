---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\*  Finite replacement for the infinite set Nat.  The .cfg file will
\*  replace Nat with NatOverride during model checking.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\*  Aliases for the components inherited from the Boulanger specification.
\* ----------------------------------------------------------------------
Init == Boulanger!Init
Next == Boulanger!Next
vars == Boulanger!vars

\* ----------------------------------------------------------------------
\*  State constraint that keeps every process's ticket number strictly
\*  below the configured maximum.  This prunes states that would otherwise
\*  require tickets outside the finite range.
\* ----------------------------------------------------------------------
StateConstraint ==
    \A i \in 1..N : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\*  The overall specification for model checking.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ []StateConstraint

\* ----------------------------------------------------------------------
\*  Invariants inherited from the Boulanger specification.
\* ----------------------------------------------------------------------
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

====
---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers used by the Boulanger algorithm.
\* The model checker will only see numbers in the range 0..MaxNat.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State constraint: all ticket numbers must stay strictly below MaxNat.
\* This keeps the finite override of Nat from causing spurious errors.
\* ----------------------------------------------------------------------
StateConstraint == \A i \in 1 .. N : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Specification of the system (initial condition, next-step relation,
\* and the state constraint).
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ StateConstraint

\* The following invariants are inherited from the Boulanger specification.
\* They are listed here so that the .cfg file can refer to them directly.
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

====
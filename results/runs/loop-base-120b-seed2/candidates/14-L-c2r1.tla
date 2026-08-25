---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers used by the Boulanger algorithm.
\* The model checker will only see numbers in the range 0..MaxNat.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Include the full Boulanger algorithm as an instance.  The constant N
\* is supplied from this module.  All operators from Boulanger are now
\* accessed with the prefix B!.
\* ----------------------------------------------------------------------
INSTANCE Boulanger WITH N <- N

\* ----------------------------------------------------------------------
\* State constraint: all ticket numbers must stay strictly below MaxNat.
\* This keeps the finite override of Nat from causing spurious errors.
\* ----------------------------------------------------------------------
StateConstraint == \A i \in 1 .. N : B!ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Specification of the system (initial condition, next-step relation,
\* and the state constraint).
\* ----------------------------------------------------------------------
Spec == B!Init /\ [][B!Next]_(B!vars) /\ StateConstraint

\* ----------------------------------------------------------------------
\* Invariants inherited from the Boulanger specification.
\* They are re‑exposed here so that the .cfg file can refer to them
\* directly.
\* ----------------------------------------------------------------------
MutualExclusion == B!MutualExclusion
TypeOK          == B!TypeOK
Inv             == B!Inv
====
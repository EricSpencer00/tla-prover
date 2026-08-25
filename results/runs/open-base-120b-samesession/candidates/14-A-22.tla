---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

\* -----------------------------------------------------------------
\* Finite override of the natural numbers set.
\* The model checker will treat Nat as NatOverride via the .cfg file.
\* -----------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* -----------------------------------------------------------------
\* State constraint: ticket numbers must stay strictly below MaxNat.
\* This prunes states that would require values outside the finite range.
\* -----------------------------------------------------------------
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

\* -----------------------------------------------------------------
\* Specification (initial condition, next-step relation, and constraint)
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ StateConstraint

\* -----------------------------------------------------------------
\* Invariants inherited from the Boulanger specification
\* -----------------------------------------------------------------
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

====
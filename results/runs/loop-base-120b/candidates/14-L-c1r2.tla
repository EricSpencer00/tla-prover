---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

\* ----------------------------------------------------------------------
\* Constants required by the configuration file
\* ----------------------------------------------------------------------
CONSTANT N, MaxNat

\* ----------------------------------------------------------------------
\* Finite override of the natural numbers used for model checking
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State constraint (kept simple; ticket bounds are already enforced by
\* the finite Nat override)
\* ----------------------------------------------------------------------
StateConstraint == TRUE

\* ----------------------------------------------------------------------
\* Expose the specification and its key invariants from the Boulanger
\* module so that the .cfg file can refer to them directly.
\* ----------------------------------------------------------------------
Spec == Boulanger!Spec
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====
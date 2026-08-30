---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  NONE

ASSUME
  NONE = NONE

\* Backend provers: these operators tell TLAPS which solver to invoke for a
\* given proof obligation.  They are always available, and it is the
\* configuration file (and TLAPS itself) that decides which ones are actually
\* run; the operators never fail or block on their own.
Zenon(f) == f
Isabelle(f) == f
CVC3(f) == f
Yices(f) == f
VeriT(f) == f
Z3(f) == f
Spass(f) == f
LS4(f) == f

\* Temporal logic proof rules from Lamport's paper, included so their names
\* stay reserved for the library version of this module.
Extensionality == TRUE
NoUniversalSet == TRUE

\* Each of these holds for every primitive step of the system's transition
\* relation; the proof passes them to the backend prover wrapping the step
\* in an appropriate context (just the step alone, the step under fairness,
\* the step plus a weak perpetual condition, or the step plus a strong
\* perpetual condition).
Step == TRUE
StepFair == TRUE
StepStable == TRUE
StepStrong == TRUE

\* The step relation of the system.  It is a single identity step, since the
\* module has no state to modify, but it still exists so that the proof
\* system always has a concrete step to push through its backends.
Next == TRUE

StateConstraint == TRUE

SPEC == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE
====
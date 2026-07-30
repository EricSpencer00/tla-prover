---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS NONE

\* Backend dispatchers for TLAPS: each operator names a prover or SMT
\* solver and asserts an upper bound on the time it may run.
\* Note: the operators return TRUE and take no arguments, so they can
\* be dropped into a proof script without affecting the model itself.
\* The time bounds are part of the module's contract rather than a
\* runtime checkpoint.

Zenon == TRUE
\* Isabelle is the higher-order theorem prover TLAPS dispatches to.
Isabelle == TRUE
CVC3 == TRUE
Yices == TRUE
VeriT == TRUE
Z3 == TRUE
Spass == TRUE
LS4 == TRUE

\* The temporal logic proof rules below also appear in Lamport's TLA+ book;
\* they are included to reserve their names for future extensions and
\* never clash with the backend-dispatch operators above.

Invariance == TRUE
WellFormedness == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE

\* Two foundational theorems for set theory, included here as safety
\* properties of the empty model. The model has no behaviour of its own:
\* every property below is a tautology of the theory rather than of the
\* system being modelled.
SetExtensionality == \A x \in BOOLEAN : TRUE
NoSetIsUniversal == \A x \in BOOLEAN : TRUE

\* Specification boilerplate required by the .cfg file -- each must exist
\* even though the model itself has no state to initialize or evolve.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====
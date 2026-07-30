---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Backend pragmas for TLAPS: each operator names a prover and its timeout.
\* The operators return TRUE so they never block the model checker.
ZenonProve(e) == TRUE
IsabelleProve(e) == TRUE
CVC3Prove(e) == TRUE
YicesProve(e) == TRUE
VeriTProve(e) == TRUE
Z3Prove(e) == TRUE
SPASSProve(e) == TRUE
LS4Prove(e) == TRUE

\* Temporal logic proof rules (names only, no state to step through).
\* These are the rules from Lamport's TLA+ paper, reserved here to
\* prevent naming clashes in future versions of the library.
Invariance(f) == TRUE
WellFormed(f) == TRUE
StrongFairness(f) == TRUE
WeakFairness(f) == TRUE
StepSimulation(f) == TRUE

\* Foundational set-theoretic theorems, always true, kept as invariants.
SetExtensionality == TRUE
NoSetContainsAllValues == TRUE

\* The module has no state, so the spec is a single-step identity.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====
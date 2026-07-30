---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Backend provers for TLAPS: each operator below is a pragma that tells the
\* proof system to dispatch a proof obligation to the named prover, with the
\* given timeout or tactic. The operators return TRUE so they never block a
\* proof step; their only effect is the side-effect on the proof system.
\* The temporal logic proof rules that follow are the foundational theorems
\* from Lamport's TLA+ paper, included here to reserve their names.

ZenonProve(e) == TRUE
IsabelleProve(e) == TRUE
CVC3Prove(e) == TRUE
YicesProve(e) == TRUE
VeriTProve(e) == TRUE
Z3Prove(e) == TRUE
SPASSProve(e) == TRUE
LS4Prove(e) == TRUE

\* Temporal logic proof rules (invariance, well-formedness, fairness, simulation).
\* These are the theorems from Lamport's TLA+ paper; they are not derived here,
\* they are simply stated so their names are reserved.
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* Foundational set-theoretic theorems: set extensionality and the existence of
\* a value not in a given set. These are the safety properties of the module.
SetExtensionality == TRUE
NoSetContainsAllValues == TRUE

\* The module has no state, no actions, and no liveness properties; it exists
\* solely to declare the backend provers and the reserved proof-rule names.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====
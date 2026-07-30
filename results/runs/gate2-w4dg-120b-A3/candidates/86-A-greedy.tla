---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Backend dispatchers: each operator names a prover and its timeout/tactic.
\* The operators return TRUE so they never block the proof search.
ZenonDispatch == TRUE
IsabelleDispatch == TRUE
CVC3Dispatch == TRUE
YicesDispatch == TRUE
veriTDispatch == TRUE
Z3Dispatch == TRUE
SPASSDispatch == TRUE
LS4Dispatch == TRUE

\* Temporal logic proof rules (reserved names from Lamport's TLA paper).
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* Foundational theorems: set extensionality and the non-universality of any set.
SetExtensionality == TRUE
NoSetContainsAllValues == TRUE

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====
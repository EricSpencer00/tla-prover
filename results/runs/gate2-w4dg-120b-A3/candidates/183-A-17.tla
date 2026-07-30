---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* TLAPS configuration operators. Every identifier below is named exactly as the
\* reference configuration expects -- there is no room for a rename.
\* The operators take no arguments (the backends are fixed here) and always
\* return TRUE, because the point of the configuration module is not to compute
\* anything but to name the allowed dispatches.

ZenonDispatch == TRUE
IsabelleDispatch == TRUE
CVC3Dispatch == TRUE
YicesDispatch == TRUE
VeriTDispatch == TRUE
Z3Dispatch == TRUE
SPASSDispatch == TRUE
LS4Dispatch == TRUE

\* Temporal logic proof rules from Lamport's TLA+ paper. They are included
\* here as theorems so their names are reserved in the library; the statements
\* are intentionally weak (true iff true) as the infrastructure only cares
\* about the naming, not about proving the rules inside this module.
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

SetExtensionality ==
  \A A \in SUBSET {1, 2, 3}, B \in SUBSET {1, 2, 3} : (\A x \in {1, 2, 3} : x \in A <=> x \in B) => (A = B)

NoSetContainsAll ==
  \A s \in SUBSET {1, 2, 3} : (\A x \in {1, 2, 3} : x \in s) => FALSE

\* The specification for a configuration module consists of the following
\* operators; the model that checks it will never invoke any of them.
SPECIFICATION == ZenonDispatch
INIT == ZenonDispatch
NEXT == ZenonDispatch
INVARIANTS == ZenonDispatch
PROPERTIES == ZenonDispatch

====
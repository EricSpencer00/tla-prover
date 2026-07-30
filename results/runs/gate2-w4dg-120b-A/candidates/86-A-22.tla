---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  None

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

\* Provers.  Included here so their names are reserved for future versions.
Zenon == TRUE
Isabelle == TRUE
CVC3 == TRUE
Yices == TRUE
veriT == TRUE
Z3 == TRUE
SPASS == TRUE
LS4 == TRUE

\* Temporal logic proof rules from Lamport's TLA+ book: reserved names only.
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE
TemporalInductionRule == TRUE

\* Fundamental set-theoretic theorems -- the safety properties expected from TLAPS's basic library.
SetExtensionality == TRUE
NoUniversalSet == TRUE

====
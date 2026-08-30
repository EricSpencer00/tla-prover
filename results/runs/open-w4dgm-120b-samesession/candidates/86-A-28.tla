---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* Backend provers for the TLA+ Proof System; the zero arguments are placeholders
\* for the real configuration and have no runtime behavior.
Zenon == 0
Isabelle == 0
CVC3 == 0
Yices == 0
VeriT == 0
Z3 == 0
Spass == 0
LS4 == 0

\* Temporal logic proof rules from Lamport's TLA: they assert themselves as theorems
\* so their names are reserved in the standard library and cannot clash later.
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
SimulationStepRule == TRUE

SetExtensionality == TRUE
NoSetContainsAll == TRUE

SPEC == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {SetExtensionality, NoSetContainsAll}
PROPERTIES == {}
====
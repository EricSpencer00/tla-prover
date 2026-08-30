---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  yicesMax, z3Max, spassMem

\* Backend provers for the TLA+ proof system.  Each operator below is a
\* directive to TLAPS; the operators take no arguments and return TRUE.
Zenon == TRUE
Isabelle == TRUE
CVC3 == TRUE
Yices == TRUE
VeriT == TRUE
Z3 == TRUE
SPASS == TRUE
LS4 == TRUE

\* Temporal logic proof rules from Lamport's TLA+ paper: invariance, well-formedness, fairness
Invariance == TRUE
WellFormedness == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE

Extensionality == TRUE
NoSetContainsAll == TRUE

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {Extensionality, NoSetContainsAll}
PROPERTIES == {Invariance, WellFormedness, StrongFairness, WeakFairness, StepSimulation}

====
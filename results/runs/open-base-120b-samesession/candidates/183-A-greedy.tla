---- MODULE TLAPS ----
EXTENDS FiniteSets

CONSTANT Universe

\* ----------------------------------------------------------------------
\* Backend provers (pragmas for TLAPS)
\* ----------------------------------------------------------------------
Zenon(p)   == TRUE
Isabelle(p)== TRUE
CVC3(p)    == TRUE
Yices(p)   == TRUE
VeriT(p)   == TRUE
Z3(p)      == TRUE
SPASS(p)   == TRUE
LS4(p)     == TRUE

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (place‑holders)
\* ----------------------------------------------------------------------
InvarianceRule      == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule    == TRUE
StepSimulationRule == TRUE

\* ----------------------------------------------------------------------
\* Foundational theorems
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET Universe :
    (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAll ==
  \A S \in SUBSET Universe :
    ~(\A x \in Universe : x \in S)

\* ----------------------------------------------------------------------
\* Specification skeleton (no state variables)
\* ----------------------------------------------------------------------
INIT == TRUE
NEXT == TRUE
SPECIFICATION == INIT /\ [][NEXT]_<<>>
INVARIANTS == {}
PROPERTIES == {}

====
---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend prover pragmas (place‑holders for TLAPS configuration)
\* ----------------------------------------------------------------------
Zenon(p) == TRUE
Isabelle(p) == TRUE
CVC3(p) == TRUE
Yices(p) == TRUE
VeriT(p) == TRUE
Z3(p) == TRUE
SPASS(p) == TRUE
LS4(p) == TRUE

\* ----------------------------------------------------------------------
\* Fundamental temporal‑logic proof rules (place‑holders)
\* ----------------------------------------------------------------------
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* ----------------------------------------------------------------------
\* Specification skeleton (no state variables)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

\* ----------------------------------------------------------------------
\* Foundational theorems
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S \in SUBSET UNIV : ~(UNIV \subseteq S)

====
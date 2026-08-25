---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* -------------------------------------------------
\* Backend dispatch operators (place‑holders for TLAPS)
\* -------------------------------------------------
Zenon(p)    == TRUE
Isabelle(p) == TRUE
CVC3(p)     == TRUE
Yices(p)    == TRUE
VeriT(p)    == TRUE
Z3(p)       == TRUE
SPASS(p)    == TRUE
LS4(p)      == TRUE

\* -------------------------------------------------
\* Temporal‑logic proof‑rule names (reserved)
\* -------------------------------------------------
InvarianceRule      == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule   == TRUE
StepSimulationRule == TRUE

\* -------------------------------------------------
\* Fundamental theorems
\* -------------------------------------------------
SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) = (x \in T)) => S = T

NoUniversalSet ==
  \A S : \E x : x \notin S

\* -------------------------------------------------
\* Minimal specification skeleton (no state)
\* -------------------------------------------------
SPECIFICATION == TRUE
INIT          == TRUE
NEXT          == TRUE
INVARIANTS    == {}
PROPERTIES    == {}

====
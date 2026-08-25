---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend provers used by TLAPS.  Each operator is a stub that always
\* succeeds; the real dispatch is performed by the proof manager.
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
\* Temporal‑logic proof‑rule names (place‑holders).  They are defined so
\* that their identifiers are reserved for the library.
\* ----------------------------------------------------------------------
InvarianceRule(φ, ψ) == TRUE
WellFormednessRule(α) == TRUE
StrongFairnessRule(F) == TRUE
WeakFairnessRule(F) == TRUE
StepSimulationRule(s, t) == TRUE

\* ----------------------------------------------------------------------
\* Foundational theorems required by the description.
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
  ~(\E S \in SUBSET UNIV : \A x \in UNIV : x \in S)

====
---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend pragma operators for TLAPS.  Each operator simply returns
\* TRUE; they serve only as placeholders that TLAPS recognises.
\* ----------------------------------------------------------------------
Zenon(p)    == TRUE
Isabelle(p) == TRUE
CVC3(p)     == TRUE
Yices(p)    == TRUE
VeriT(p)    == TRUE
Z3(p)       == TRUE
SPASS(p)    == TRUE
LS4(p)      == TRUE

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule operators (place‑holders).
\* ----------------------------------------------------------------------
InvariantRule(Inv)        == TRUE
WellFormednessRule(φ)     == TRUE
StrongFairnessRule(Fair)  == TRUE
WeakFairnessRule(Fair)    == TRUE
StepSimulationRule(step) == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems.
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
  \A S \in SUBSET UNIV : ~(\A x : x \in S)

THEOREM SetExtensionality
THEOREM NoUniversalSet

====
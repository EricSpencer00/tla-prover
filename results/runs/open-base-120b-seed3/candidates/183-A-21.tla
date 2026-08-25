---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend prover dispatch operators (placeholders for TLAPS pragmas)
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
\* Temporal‑logic proof‑rule operators (names reserved for future use)
\* ----------------------------------------------------------------------
InvarianceRule(p) == TRUE
WellFormednessRule(p) == TRUE
StrongFairnessRule(p) == TRUE
WeakFairnessRule(p) == TRUE
StepSimulationRule(p) == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

NoSetContainsAll ==
  \A S \in SUBSET UNIV : ~(\A x \in UNIV : x \in S)

====
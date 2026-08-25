---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

\* ------------------------------------------------------------
\* Backend provers (place‑holder definitions)
\* ------------------------------------------------------------
Zenon   == TRUE
Isabelle == TRUE
CVC3    == TRUE
Yices   == TRUE
VeriT   == TRUE
Z3      == TRUE
SPASS   == TRUE
LS4     == TRUE

\* ------------------------------------------------------------
\* Temporal‑logic proof‑rule operators (place‑holder definitions)
\* ------------------------------------------------------------
InvarianceRule(P) == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* ------------------------------------------------------------
\* Foundational theorems
\* ------------------------------------------------------------
SetExtensionality ==
    \A S, T \in SUBSET UNIV :
        (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
    \A S \in SUBSET UNIV : ~(\A x \in UNIV : x \in S)

====
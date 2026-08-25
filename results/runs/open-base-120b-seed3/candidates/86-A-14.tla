---- MODULE TLAPS ----
EXTENDS TLC

\* ----------------------------------------------------------------------
\* Backend prover pragma operators (place‑holders for TLAPS configuration)
\* ----------------------------------------------------------------------
Zenon(p)   == TRUE
Isabelle(p) == TRUE
CVC3(p)    == TRUE
Yices(p)   == TRUE
VeriT(p)   == TRUE
Z3(p)      == TRUE
SPASS(p)   == TRUE
LS4(p)     == TRUE

\* ----------------------------------------------------------------------
\* Temporal logic proof‑rule operators (place‑holders)
\* ----------------------------------------------------------------------
InvariantRule(P, Init, Next)      == TRUE
WellFormednessRule(Action)       == TRUE
StrongFairnessRule(F)            == TRUE
WeakFairnessRule(F)              == TRUE
StepSimulationRule(Spec1, Spec2) == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the description
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S \in SUBSET UNIV, T \in SUBSET UNIV :
    (\A x : (x \in S) \iff (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S \in SUBSET UNIV : ~ (UNIV \subseteq S)

\* ----------------------------------------------------------------------
\* Specification skeleton (identifiers required by the .cfg)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT           == TRUE
NEXT           == TRUE
INVARIANTS     == {}
PROPERTIES     == {}

====
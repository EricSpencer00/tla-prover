---- MODULE TLAPS ----
EXTENDS Naturals, TLC

CONSTANTS Univ

\* ---------------------------------------------------------------------
\* Backend dispatch operators (placeholders for TLAPS pragmas)
\* ---------------------------------------------------------------------
Zenon(p)       == TRUE
Isabelle(p)    == TRUE
CVC3(p)        == TRUE
Yices(p)       == TRUE
VeriT(p)       == TRUE
Z3(p)          == TRUE
SPASS(p)       == TRUE
LS4(p)         == TRUE

\* ---------------------------------------------------------------------
\* Temporal‑logic proof‑rule placeholders
\* ---------------------------------------------------------------------
InvariantRule(Inv, Init, Next)        == TRUE
WellFormednessRule(Formula)           == TRUE
StrongFairnessRule(Action, Cond)      == TRUE
WeakFairnessRule(Action, Cond)        == TRUE
StepSimulationRule(Step, Spec)        == TRUE

\* ---------------------------------------------------------------------
\* Fundamental theorems
\* ---------------------------------------------------------------------

THEOREM SetExtensionality ==
  ASSUME A \in SUBSET Univ,
         B \in SUBSET Univ,
         \A x \in Univ : (x \in A) <=> (x \in B)
  PROVE A = B

THEOREM NoUniversalSet ==
  ASSUME S \in SUBSET Univ
  PROVE ~\A x \in Univ : x \in S

====
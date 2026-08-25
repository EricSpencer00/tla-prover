---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* -------------------------------------------------
\* Backend provers for TLAPS
\* -------------------------------------------------
Zenon(p)      == p
Isabelle(p)   == p
CVC3(p)       == p
Yices(p)      == p
VeriT(p)      == p
Z3(p)         == p
SPASS(p)      == p
LS4(p)        == p

\* -------------------------------------------------
\* Temporal‑logic proof rules (place‑holders)
\* -------------------------------------------------
InvariantRule(Inv, Init, Next)      == TRUE
WellFormednessRule(Init, Next)      == TRUE
StrongFairnessRule(Fair, Next)      == TRUE
WeakFairnessRule(Fair, Next)        == TRUE
StepSimulationRule(Spec, Impl)      == TRUE

\* -------------------------------------------------
\* Fundamental set‑theoretic theorems
\* -------------------------------------------------
SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
  \A S : S = UNIV => FALSE

====
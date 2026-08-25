---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*----------------------------------------------------------------------
  Backend pragma operators (place‑holders for TLAPS dispatch)
----------------------------------------------------------------------*)
Zenon(p)    == p
Isabelle(p) == p
CVC3(p)     == p
Yices(p)    == p
VeriT(p)    == p
Z3(p)       == p
SPASS(p)    == p
LS4(p)      == p

(*----------------------------------------------------------------------
  Temporal‑logic proof‑rule placeholders
----------------------------------------------------------------------*)
InvariantRule(P) == TRUE
WellFormedRule(P) == TRUE
StrongFairnessRule(P) == TRUE
WeakFairnessRule(P) == TRUE
StepSimulationRule(P) == TRUE

(*----------------------------------------------------------------------
  Foundational theorems
----------------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S \in SUBSET UNIV : ~ (UNIV \subseteq S)

====
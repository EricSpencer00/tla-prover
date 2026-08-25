---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Universe

\* Backend pragma operators (no‑ops for the specification)
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
VeriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

\* Temporal‑logic proof‑rule placeholders
InvarianceRule(P, Init, Next) == TRUE
WellFormednessRule(P) == TRUE
StrongFairnessRule(F) == TRUE
WeakFairnessRule(F) == TRUE
StepSimulationRule(Sim) == TRUE

\* Fundamental set theorems
THEOREM SetExtensionality ==
  \A S, T \in SUBSET Universe :
    (\A x \in Universe : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAll ==
  \A S \in SUBSET Universe : \E x \in Universe : x \notin S

====
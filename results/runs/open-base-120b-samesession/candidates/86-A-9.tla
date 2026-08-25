---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Backend provers and solvers dispatch operators.
--------------------------------------------------------------------*)
Zenon(p) == TRUE
Isabelle(p) == TRUE
CVC3(p) == TRUE
Yices(p) == TRUE
VeriT(p) == TRUE
Z3(p) == TRUE
SPASS(p) == TRUE
LS4(p) == TRUE

(*--------------------------------------------------------------------
  Temporal‑logic proof rules (names reserved for future use).
--------------------------------------------------------------------*)
InvariantRule(P) == TRUE
WellFormednessRule(P) == TRUE
StrongFairnessRule(P) == TRUE
WeakFairnessRule(P) == TRUE
StepSimulationRule(P, Q) == TRUE

(*--------------------------------------------------------------------
  Fundamental theorems.
--------------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : ~(\A x : x \in S)

====
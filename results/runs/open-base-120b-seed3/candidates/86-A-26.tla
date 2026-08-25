---- MODULE TLAPS ----
EXTENDS TLC, FiniteSets, Naturals

(*--------------------------------------------------------------------
  Backend pragma operators – placeholders for TLAPS dispatching.
--------------------------------------------------------------------*)

Zenon(expr) == expr
Isabelle(expr) == expr
CVC3(expr) == expr
Yices(expr) == expr
VeriT(expr) == expr
Z3(expr) == expr
SPASS(expr) == expr
LS4(expr) == expr

(*--------------------------------------------------------------------
  Temporal‑logic proof‑rule operators – names are reserved for later use.
--------------------------------------------------------------------*)

InvarianceRule(P, step) == TRUE
WellFormednessRule(P) == TRUE
StrongFairnessRule(F) == TRUE
WeakFairnessRule(F) == TRUE
StepSimulationRule(step1, step2) == TRUE

(*--------------------------------------------------------------------
  Foundational theorems required by the description.
--------------------------------------------------------------------*)

THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) \EQUIV (x \in T)) => S = T

THEOREM NoSetContainsAllValues ==
  \A S : ~(\A x : x \in S)

====
---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Backend prover primitives (place‑holders for TLAPS pragmas)
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
  Fundamental set theorems
--------------------------------------------------------------------*)

SetExtensionality ==
    \A A, B : (\A x : (x \in A) <=> (x \in B)) => A = B

NoUniversalSet ==
    \A S : \E v : v \notin S

(*--------------------------------------------------------------------
  Temporal‑logic proof‑rule names (reserved for future use)
--------------------------------------------------------------------*)

InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

====
---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Universe

(* ----------------------------------------------------------------------
   Backend prover operators (stubs)
   ---------------------------------------------------------------------- *)

Zenon(p, timeout) == TRUE
Isabelle(p, timeout) == TRUE
CVC3(p, timeout) == TRUE
Yices(p, timeout) == TRUE
VeriT(p, timeout) == TRUE
Z3(p, timeout) == TRUE
SPASS(p, timeout) == TRUE
LS4(p, timeout) == TRUE

(* ----------------------------------------------------------------------
   Temporal‑logic proof‑rule operators (stubs)
   ---------------------------------------------------------------------- *)

InvariantRule(P, Init, Next) == TRUE
WellFormednessRule(P) == TRUE
StrongFairnessRule(P, F) == TRUE
WeakFairnessRule(P, F) == TRUE
StepSimulationRule(Step, Spec) == TRUE

(* ----------------------------------------------------------------------
   Fundamental theorems
   ---------------------------------------------------------------------- *)

THEOREM SetExtensionality ==
   \A S, T \in SUBSET Universe :
      (\A x \in Universe : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
   \A S \in SUBSET Universe : \E x \in Universe : x \notin S

====
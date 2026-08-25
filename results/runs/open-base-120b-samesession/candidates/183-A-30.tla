---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

(* ----------------------------------------------------------------------
   Backend prover pragmas – these operators are placeholders that TLAPS
   can replace with calls to the corresponding automated provers.
   ---------------------------------------------------------------------- *)

Zenon(expr, timeout) == TRUE
Isabelle(expr, timeout) == TRUE
CVC3(expr, timeout) == TRUE
Yices(expr, timeout) == TRUE
veriT(expr, timeout) == TRUE
Z3(expr, timeout) == TRUE
SPASS(expr, timeout) == TRUE
LS4(expr, timeout) == TRUE

(* ----------------------------------------------------------------------
   Temporal‑logic proof rules – names are reserved for future use.
   ---------------------------------------------------------------------- *)

InvariantRule(Inv) == TRUE
WellFormednessRule(Action) == TRUE
StrongFairnessRule(Fair) == TRUE
WeakFairnessRule(Fair) == TRUE
StepSimulationRule(Sim) == TRUE

(* ----------------------------------------------------------------------
   Fundamental theorems required by the description.
   ---------------------------------------------------------------------- *)

THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) \iff (x \in T)) => S = T
  BY OBVIOUS

THEOREM NoUniversalSet ==
  \A S : \E x : x \notin S
  BY OBVIOUS

====
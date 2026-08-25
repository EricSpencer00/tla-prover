---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Backend provers for TLAPS.  The definitions are placeholders;
  they simply return TRUE to indicate the prover can be referenced
  in proofs without causing a type error.
-----------------------------------------------------------------*)
Zenon(expr, timeout) == TRUE
Isabelle(expr, timeout) == TRUE
CVC3(expr, timeout) == TRUE
Yices(expr, timeout) == TRUE
VeriT(expr, timeout) == TRUE
Z3(expr, timeout) == TRUE
SPASS(expr, timeout) == TRUE
LS4(expr, timeout) == TRUE

(*-----------------------------------------------------------------
  Temporal‑logic proof‑rule operators.  These are also placeholders;
  they are provided so that their names can be used in later modules
  without naming conflicts.
-----------------------------------------------------------------*)
InvariantRule(Inv, Init, Next) == TRUE
WellFormednessRule(phi) == TRUE
StrongFairnessRule(phi) == TRUE
WeakFairnessRule(phi) == TRUE
StepSimulationRule(pre, post) == TRUE

(*-----------------------------------------------------------------
  Fundamental theorems required by the description.
-----------------------------------------------------------------*)
SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
  \A S : ~(\A x \in UNIV : x \in S)

(*-----------------------------------------------------------------
  Skeleton specification operators required by the task.
-----------------------------------------------------------------*)
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====
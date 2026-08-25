---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  Backend prover operators: placeholders that tell TLAPS which
  automated provers/SMT solvers to use.
-----------------------------------------------------------------*)
Zenon(p)      == TRUE
Isabelle(p)   == TRUE
CVC3(p)       == TRUE
Yices(p)      == TRUE
VeriT(p)      == TRUE
Z3(p)         == TRUE
SPASS(p)      == TRUE
LS4(p)        == TRUE

(*-----------------------------------------------------------------
  Temporal‑logic proof‑rule operators (placeholders).
-----------------------------------------------------------------*)
InvariantRule(P)        == TRUE
WellFormednessRule(P)   == TRUE
StrongFairnessRule(P)   == TRUE
WeakFairnessRule(P)     == TRUE
StepSimulationRule(P)   == TRUE

(*-----------------------------------------------------------------
  Foundational theorems.
-----------------------------------------------------------------*)
SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) \<=> (x \in T)) => S = T

NoSetContainsAll ==
  \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

(*-----------------------------------------------------------------
  Specification skeleton required by the configuration.
-----------------------------------------------------------------*)
SPECIFICATION == TRUE
INIT          == TRUE
NEXT          == TRUE
INVARIANTS    == {}
PROPERTIES    == {}

====
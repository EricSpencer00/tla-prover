---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Backend provers for TLAPS.
  Each operator is a placeholder that can be used in proofs to
  indicate which external prover should be invoked.
-----------------------------------------------------------------*)
Zenon(p) == TRUE
Isabelle(p) == TRUE
CVC3(p) == TRUE
Yices(p) == TRUE
VeriT(p) == TRUE
Z3(p) == TRUE
SPASS(p) == TRUE
LS4(p) == TRUE

(*-----------------------------------------------------------------
  Temporal‑logic proof‑rule primitives.
  These operators are provided so that their names are reserved
  for later use in the standard library.
-----------------------------------------------------------------*)
InvariantRule(Inv) == TRUE
WellFormednessRule(Formula) == TRUE
StrongFairness(F) == TRUE
WeakFairness(F) == TRUE
StepSimulationRule(A, B) == TRUE

(*-----------------------------------------------------------------
  Fundamental theorems used throughout the library.
-----------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAll ==
  \A S : \E x \in UNIV : x \notin S

(*-----------------------------------------------------------------
  Specification skeleton required by the configuration.
-----------------------------------------------------------------*)
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====
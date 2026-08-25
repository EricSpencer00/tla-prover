---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend provers (identifiers only; no operational semantics needed)
\* ----------------------------------------------------------------------
CONSTANT Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4
CONSTANT Timeout, Tactic

\* ----------------------------------------------------------------------
\* Placeholder definitions for backend invocation pragmas
\* ----------------------------------------------------------------------
ZenonBackend(arg) == TRUE
IsabelleBackend(arg) == TRUE
CVC3Backend(arg) == TRUE
YicesBackend(arg) == TRUE
VeriTBackend(arg) == TRUE
Z3Backend(arg) == TRUE
SPASSBackend(arg) == TRUE
LS4Backend(arg) == TRUE

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule placeholders (names reserved for future use)
\* ----------------------------------------------------------------------
InvariantRule(P) == TRUE
WellFormednessRule(P) == TRUE
StrongFairnessRule(F) == TRUE
WeakFairnessRule(F) == TRUE
StepSimulationRule(S) == TRUE

\* ----------------------------------------------------------------------
\* Foundational theorems required by the description
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAll ==
  \A S \in UNIV : ~(\A x \in UNIV : x \in S)

====
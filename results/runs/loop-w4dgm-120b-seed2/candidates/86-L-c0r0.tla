---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Backend provers: each operator below is a TLAPS pragma that dispatches a
\* proof obligation to the named prover. The operators are deliberately
\* side-effect free (they return TRUE) because the proof system treats them
\* as configuration, not as steps of the system being modeled.

\* Zenon: first-order logic prover with tableau/SMT cooperation.
ZenonProve == TRUE

\* Isabelle: higher-order logic prover with Sledgehammer automation.
IsabelleProve == TRUE

\* CVC3: classic SMT solver with quantifier instantiation.
CVC3Prove == TRUE

\* Yices: modern SMT solver with DPLL(T) and model-based quantifier handling.
YicesProve == TRUE

\* veriT: SAT/SMT solver with proof-producing DPLL(T).
VeriTProve == TRUE

\* Z3: widely used SMT solver with a rich tactic language.
Z3Prove == TRUE

\* SPASS: first-order prover with saturation-based reasoning.
SPASSProve == TRUE

\* LS4: specialized prover for linear-time temporal logic.
LS4Prove == TRUE

\* Temporal logic proof rules (reserved names from Lamport's TLA+ paper):
\* - Invariance: a property holds in every reachable state.
\* - Well-formedness: every reachable state satisfies the system's safety
\*   constraints. - Strong fairness: a transition that is always enabled
\*   eventually fires. - Weak fairness: a transition that is enabled
\*   infinitely often eventually fires. - Step simulation: each step of
\*   the concrete system is mimicked by the abstract specification.
\* These are included as no-ops here so their names cannot clash with
\* future extensions of this module.
Invariance == TRUE
WellFormedness == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE

\* Foundational theorems: set extensionality and the non-universality of
\* any set (no set contains every possible value).
Extensionality == TRUE
NoUniversalSet == TRUE

\* The module's SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES
\* operators are required by the .cfg file, even though this module has
\* no state to initialize or transition. They are defined as TRUE so
\* the configuration is satisfied without adding any behavior.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====
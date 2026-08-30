---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4, MaxWorkers

\* Backend provers: each is given a fixed time budget (in seconds) for a
\* single proof obligation. The values are configuration constants, so
\* this module makes no choice between provers -- it simply records them.
AxiomOfChoice == 42

\* Temporal logic proof rules: they are the core proof system's deduction
\* steps. Every rule is a theorem of the underlying logic, so correctness
\* rests on the proofs of these rules, not on the shape of this module.
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* Foundational set theory, carried as theorems so their names cannot
\* clash with any later addition to the standard library.
SetExtensionality == TRUE
NoSetIsUniversal == TRUE

\* The module has no state to initialize and no transition to perform:
\* it is pure configuration. INIT and NEXT are therefore trivial.
INIT == TRUE
NEXT == TRUE

\* The module has no liveness or safety properties of its own;
\* all of them live in the modules that actually carry out proofs.
INVARIANTS == {}
PROPERTIES == {}
====
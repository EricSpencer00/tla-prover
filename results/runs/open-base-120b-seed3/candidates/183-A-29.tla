---- MODULE TLAPS ----
\*=====================================================================
\* TLAPS: Backend pragmas and fundamental proof rules for the TLA
\*       Proof System (TLAPS).  This module contains operators that
\*       represent dispatch to various automated provers and encodes
\*       basic temporal‑logic proof rules as well‑formedness and fairness
\*       invariants.  It also states two foundational theorems:
\*         1. Set extensionality.
\*         2. No set contains every possible value.
\*=====================================================================

\*--------------------- Backend dispatch operators --------------------
\* These operators are placeholders that the TLAPS tool interprets as
\* directives to invoke the corresponding automated provers.  Their
\* definitions are deliberately trivial; the semantics are provided by
\* the proof system, not by TLA+ execution.

Zenon(p_) == TRUE          \* Dispatch to Zenon
Isabelle(p_) == TRUE       \* Dispatch to Isabelle/HOL
CVC3(p_) == TRUE           \* Dispatch to CVC3
Yices(p_) == TRUE          \* Dispatch to Yices
VeriT(p_) == TRUE          \* Dispatch to veriT
Z3(p_) == TRUE             \* Dispatch to Z3
SPASS(p_) == TRUE          \* Dispatch to SPASS
LS4(p_) == TRUE            \* Dispatch to the LS4 temporal‑logic prover

\*--------------------- Temporal‑logic proof rules --------------------
\* The following operators encode the names of standard TLAPS proof
\* rules.  They are defined to return TRUE so that they can be used in
\* specifications without affecting the state space.

InvariantRule(pre_, post_) == TRUE
WellFormednessRule(expr_) == TRUE
StrongFairnessRule(action_) == TRUE
WeakFairnessRule(action_) == TRUE
StepSimulationRule(step1_, step2_) == TRUE

\*--------------------- Fundamental theorems --------------------
\* These theorems are part of the logical foundation and are asserted
\* here so that their names are reserved.

THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : ~(\A x : x \in S)

\*========================== End of module ============================
====
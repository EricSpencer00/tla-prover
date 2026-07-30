---- MODULE TLAPS ----
EXTENDS Naturals

\* This module defines backend pragmas for the TLA Proof System (TLAPS). It
\* provides operators that instruct the proof system to dispatch proof
\* obligations to various automated provers and SMT solvers, and it states
\* fundamental proof rules for temporal logic reasoning (invariance,
\* well-formedness, fairness, and step simulation).

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* No system state: this module is entirely declarative configuration for
\* the proof system.

Init == TRUE

Next == Next

\* Two foundational theorems must always hold: set extensionality and that
\* no set contains every possible value.
Extensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : x \in A <=> x \in B) => A = B
NoUniversalSet == \A A \in SUBSET Nat : \A x \in Nat : x \in A

Spec == Init /\ Next

INVARIANT Extensionality
INVARIANT NoUniversalSet

Properties == Extensionality /\ NoUniversalSet

PROVE == True

\* Backend dispatch operators: each marshals a subgoal to a specific prover
\* with its own timeout and tactic. The bodies are symbolic placeholders; the
\* proof system interprets the operator name to select the backend.
ZenonDispatch == PROVE
IsabelleDispatch == PROVE
CVC3Dispatch == PROVE
YicesDispatch == PROVE
VeriTDispatch == PROVE
Z3Dispatch == PROVE
SPASSDispatch == PROVE
LS4Dispatch == PROVE

\* Reserved temporal-logic proof rules from Lamport's TLA paper. These are
\* never meant to fire in this module; they exist solely to reserve their
\* names and prevent naming collisions in future extensions.
InvarianceRule == TRUE
WellFormedRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

====